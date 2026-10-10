#!/usr/bin/env node
// TT Direct — Node.js edition
// Usage:
//   node tt.js                      (interactive prompt)
//   node tt.js "cookie_string"      (inline)

const crypto = require('crypto');
const https  = require('https');
const readline = require('readline');
const { performance } = require('perf_hooks');

let WebSocket;
try {
  WebSocket = require('ws');
} catch (e) {
  console.error('\n[!] Missing dependency: ws');
  console.error('    Install with: npm install ws\n');
  process.exit(1);
}

// ============================================================
// CONFIG
// ============================================================
const CFG = {
  HOST:        'thunder-zone.coke2home.com',
  ORIGIN:      'https://thunder-zone.coke2home.com',
  REFERER:     'https://thunder-zone.coke2home.com/game',
  SESSION_URL: '/api/thunder-trail/sessions',
  WS_URL:      'wss://thunder-zone.coke2home.com/backend/api/v1/thunder-trails/ws',
  USER_AGENT:  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',

  REACT_BANDS: [
    { maxTravel: 200,      min: 220, max: 300, sigma: 25 },
    { maxTravel: 400,      min: 220, max: 320, sigma: 28 },
    { maxTravel: 800,      min: 220, max: 340, sigma: 32 },
    { maxTravel: Infinity, min: 220, max: 400, sigma: 45 }
  ],
  WIRE_BUFFER_MS:       60,
  STOP_AT_MS:           92319,

  TRAP_FAIL_PER_TIER:   1,
  TRAP_FAIL_HP_MIN:     2,
  TRAP_FAIL_MODE:       'mix'
};

const OPP = { up:'down', down:'up', left:'right', right:'left' };
const SYM = { up:'↑', down:'↓', left:'←', right:'→' };
const TSYM = { thunder:'⚡', thunder2:'⚡', gully:'👟', firefox:'🚲', heart:'❤', trap:'✗' };

function log(...a){ console.log('[TTD]', ...a); }
function err(...a){ console.error('[TTD]', ...a); }

// ============================================================
// HTTP
// ============================================================
function httpsPost(path, cookie, body){
  return new Promise((resolve, reject) => {
    const data = JSON.stringify(body || {});
    const req = https.request({
      hostname: CFG.HOST,
      port: 443,
      path,
      method: 'POST',
      headers: {
        'Content-Type':     'application/json',
        'Content-Length':   Buffer.byteLength(data),
        'Cookie':           cookie,
        'Origin':           CFG.ORIGIN,
        'Referer':          CFG.REFERER,
        'User-Agent':       CFG.USER_AGENT,
        'Accept':           'application/json, text/plain, */*',
        'Accept-Language':  'en-US,en;q=0.9',
        'Sec-Fetch-Site':   'same-origin',
        'Sec-Fetch-Mode':   'cors',
        'Sec-Fetch-Dest':   'empty'
      }
    }, res => {
      let buf = '';
      res.on('data', c => buf += c);
      res.on('end', () => resolve({ status: res.statusCode, body: buf, headers: res.headers }));
    });
    req.on('error', reject);
    req.setTimeout(20000, () => { req.destroy(new Error('timeout')); });
    req.write(data);
    req.end();
  });
}

// ============================================================
// CRYPTO
// ============================================================
function importFrameKey(b64){ return Buffer.from(b64, 'base64'); }

function signMsg(key, sid, seq, ts, type, payload){
  let inner = '';
  if (type === 'hello')      inner = `${payload.ticket ?? ''}|${payload.resume_from_seq ?? 0}`;
  else if (type === 'swipe') inner = `${payload.box_id ?? 0}|${payload.dir ?? ''}|${payload.client_at_ms ?? 0}`;
  else if (type === 'pong')  inner = payload.nonce ?? '';
  const msg = `${sid}|${seq}|${ts}|${type}|${inner}`;
  return crypto.createHmac('sha256', key).update(msg, 'utf8').digest('base64');
}

// ============================================================
// SAMPLING
// ============================================================
function bandFor(travelMs){
  const t = travelMs || 1950;
  for (const b of CFG.REACT_BANDS) if (t <= b.maxTravel) return b;
  return CFG.REACT_BANDS[CFG.REACT_BANDS.length - 1];
}
function hash01(boxId, salt){
  let h = ((boxId >>> 0) ^ (salt >>> 0)) >>> 0;
  h = Math.imul(h ^ (h >>> 16), 0x7feb352d) >>> 0;
  h = Math.imul(h ^ (h >>> 15), 0x846ca68b) >>> 0;
  h = (h ^ (h >>> 16)) >>> 0;
  return (h % 100000) / 100000;
}
function sampleReaction(boxId, travelMs){
  const band = bandFor(travelMs);
  const mu = (band.min + band.max) / 2;
  const sigma = band.sigma;
  const u1 = Math.max(1e-6, hash01(boxId, 0xA5A5));
  const u2 = hash01(boxId, 0x5A5A);
  const z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
  const raw = mu + z * sigma;
  const travel = travelMs || 1950;
  const cap = travel - CFG.WIRE_BUFFER_MS;
  return Math.max(band.min, Math.min(band.max, raw, cap));
}

// ============================================================
// STATE
// ============================================================
let sid, ticket, frameKeyBuf, cookie;
let ws = null, seq = 0, t0 = 0;
let running = false, stopped = false, sessionEnded = false;
let sessionStartAt = 0, sessionEndAt = 0;
let swipeCount = 0, hitCount = 0, missCount = 0;
let currentHp = 3, currentScore = 0, currentTierId = 1;

let trapFailThisTier = 0, trapFailTier = 1, trapFailTotal = 0;

const seenSeq = new Set();
const pending = new Map();
const timers  = new Map();

const boxCounts = { thunder:0, thunder2:0, gully:0, firefox:0, heart:0, trap:0 };
let hgBoxes = 0, hgTraps = 0, hgOthers = 0;

const TIERS = [
  { id:1,  untilMs:15000,   label:'SLOW' },
  { id:2,  untilMs:30000,   label:'MEDIUM' },
  { id:3,  untilMs:45000,   label:'FAST' },
  { id:4,  untilMs:60000,   label:'VERYFAST' },
  { id:5,  untilMs:75000,   label:'EXTREME' },
  { id:6,  untilMs:90000,   label:'INSANE' },
  { id:7,  untilMs:105000,  label:'TURBO' },
  { id:8,  untilMs:120000,  label:'NITRO' },
  { id:9,  untilMs:135000,  label:'HYPERDRIVE' },
  { id:10, untilMs:Infinity,label:'MAXSPEED' }
];
function tierFor(ms){ for (const t of TIERS) if (ms < t.untilMs) return t; return TIERS[TIERS.length - 1]; }

// ============================================================
// WS SEND
// ============================================================
async function sendSigned(type, payload){
  if (!ws || ws.readyState !== WebSocket.OPEN) return false;
  if (!frameKeyBuf) return false;
  const s = ++seq;
  const ts = Math.round(performance.now() - t0);
  const mac = signMsg(frameKeyBuf, sid, s, ts, type, payload);
  const env = { v:1, t:type, seq:s, ts, p:payload, mac };
  try { ws.send(JSON.stringify(env)); return true; }
  catch (e) { err('ws.send threw', e); return false; }
}

// ============================================================
// TRAP FAIL
// ============================================================
function shouldTrapFail(box){
  if (box.type !== 'trap') return null;
  const liveTier = tierFor(sessionStartAt ? performance.now() - sessionStartAt : 0).id;
  if (trapFailTier !== liveTier) { trapFailThisTier = 0; trapFailTier = liveTier; }
  if (trapFailThisTier >= CFG.TRAP_FAIL_PER_TIER) return null;
  if (currentHp < CFG.TRAP_FAIL_HP_MIN) return null;
  const mode = CFG.TRAP_FAIL_MODE;
  if (mode === 'miss')  return 'miss';
  if (mode === 'wrong') return 'wrong';
  return (hash01(box.id, 0xBEEF) < 0.5) ? 'miss' : 'wrong';
}

// ============================================================
// FIRE
// ============================================================
function fireSwipe(box){
  if (stopped || sessionEnded) return;
  const elapsed = sessionStartAt ? performance.now() - sessionStartAt : 0;
  if (elapsed > CFG.STOP_AT_MS){
    if (!stopped){ stopped = true; log('STOP_AT_MS reached · draining'); }
    return;
  }
  if (box.fired) return;

  const failMode = shouldTrapFail(box);
  if (failMode === 'miss'){
    box.fired = true; box.trapFailMode = 'miss';
    trapFailThisTier++; trapFailTotal++;
    log('TRAP-FAIL miss  id=' + box.id + ' hp=' + currentHp);
    return;
  }
  if (failMode === 'wrong'){
    box.fired = true; box.trapFailMode = 'wrong';
    trapFailThisTier++; trapFailTotal++;
    const clientAt = Math.round(performance.now() - t0);
    swipeCount++;
    sendSigned('swipe', { box_id: box.id, dir: box.arrow, client_at_ms: clientAt });
    log('TRAP-FAIL wrong id=' + box.id + ' arrow=' + box.arrow + ' hp=' + currentHp);
    return;
  }

  box.fired = true;
  const dir = box.type === 'trap' ? OPP[box.arrow] : box.arrow;
  const clientAt = Math.round(performance.now() - t0);
  swipeCount++;
  sendSigned('swipe', { box_id: box.id, dir, client_at_ms: clientAt });
}

// ============================================================
// FRAME HANDLER
// ============================================================
function onFrame(raw){
  let m;
  try { m = JSON.parse(raw); } catch { return; }
  if (!m || typeof m !== 'object') return;
  const t = m.t, p = m.p || {};

  if (m.seq != null){
    const k = t + ':' + m.seq;
    if (seenSeq.has(k)) return;
    seenSeq.add(k);
  }

  switch (t){
    case 'hello': case 'ready': break;

    case 'welcome':
      running = true; stopped = false; sessionEnded = false;
      sessionStartAt = performance.now();
      sessionEndAt = 0;
      swipeCount = 0; hitCount = 0; missCount = 0;
      currentHp = p.hp ?? 3;
      currentScore = p.score ?? 0;
      trapFailThisTier = 0; trapFailTier = 1; trapFailTotal = 0;
      for (const k in boxCounts) boxCounts[k] = 0;
      hgBoxes = 0; hgTraps = 0; hgOthers = 0;
      seenSeq.clear();
      for (const [,h] of timers) clearTimeout(h);
      timers.clear(); pending.clear();
      seq = 0;
      t0 = performance.now();
      log('welcome hp=' + currentHp);
      sendSigned('ready', {});
      break;

    case 'ping':
      sendSigned('pong', { nonce: p.nonce ?? '' });
      break;

    case 'pong': break;

    case 'sync':
      if (typeof p.score === 'number') currentScore = p.score;
      if (typeof p.hp === 'number'){
        if (p.hp < currentHp){ hgBoxes = 0; hgTraps = 0; hgOthers = 0; }
        currentHp = p.hp;
      }
      break;

    case 'spawn': {
      if (sessionEnded) break;
      const id = p.box_id;
      const travel = p.travel_ms || 1950;
      pending.set(id, {
        id, type: p.type, arrow: null,
        spawnAt: performance.now(),
        travelMs: travel,
        reactMs: null, fired: false, trapFailMode: null
      });
      if (boxCounts[p.type] !== undefined) boxCounts[p.type]++;
      if (p.type === 'heart'){ hgBoxes = 0; hgTraps = 0; hgOthers = 0; }
      else { hgBoxes++; if (p.type === 'trap') hgTraps++; else hgOthers++; }
      break;
    }

    case 'reveal': {
      if (sessionEnded) break;
      const b = pending.get(p.box_id);
      if (!b) break;
      b.arrow = p.arrow;
      b.reactMs = sampleReaction(b.id, b.travelMs);
      const wait = Math.max(0, b.reactMs);
      const handle = setTimeout(() => {
        timers.delete(b.id);
        fireSwipe(b);
      }, wait);
      timers.set(b.id, handle);
      break;
    }

    case 'result': {
      const b = pending.get(p.box_id);
      if (b && timers.has(p.box_id)){
        clearTimeout(timers.get(p.box_id));
        timers.delete(p.box_id);
      }
      if (b) b.resolved = true;
      if (p.outcome === 'correct') hitCount++;
      if (p.outcome === 'miss' || p.outcome === 'wrong') missCount++;
      if (typeof p.score === 'number') currentScore = p.score;
      if (typeof p.hp === 'number'){
        if (p.hp < currentHp){ hgBoxes = 0; hgTraps = 0; hgOthers = 0; }
        currentHp = p.hp;
      }
      log(
        (b ? TSYM[b.type] : '?') + ' ' + (b ? b.type : '?') +
        ' ' + (b ? SYM[b.arrow] : '?') +
        ' -> ' + p.outcome +
        '  pts=' + (p.points || 0) +
        '  score=' + currentScore +
        '  hp=' + currentHp
      );
      pending.delete(p.box_id);
      break;
    }

    case 'end':
      running = false; stopped = true; sessionEnded = true;
      sessionEndAt = performance.now();
      for (const [,h] of timers) clearTimeout(h);
      timers.clear(); pending.clear();
      console.log('');
      log('══════ END ══════');
      log('score     :', p.final_score);
      log('reason    :', p.reason);
      log('is_bot    :', p.is_bot);
      log('evidence  :', p.evidence_id || 'n/a');
      log('swipes    :', swipeCount);
      log('hits      :', hitCount);
      log('misses    :', missCount);
      log('trapFails :', trapFailTotal);
      log('boxCounts :', boxCounts);
      log('elapsed   :', sessionStartAt ? Math.round(sessionEndAt - sessionStartAt) + 'ms' : 'n/a');
      log('═════════════════');
      try { ws.close(); } catch {}
      setTimeout(() => process.exit(0), 200);
      break;

    case 'error':
      err('server error', p);
      break;
  }
}

// ============================================================
// MAIN
// ============================================================
async function run(){
  log('POST ' + CFG.SESSION_URL);
  const r = await httpsPost(CFG.SESSION_URL, cookie, {});
  if (r.status < 200 || r.status >= 300){
    err('session failed HTTP ' + r.status);
    err(r.body.slice(0, 400));
    process.exit(1);
  }

  let parsed;
  try { parsed = JSON.parse(r.body); }
  catch (e){ err('bad JSON', r.body.slice(0, 300)); process.exit(1); }

  const data = parsed.data ?? parsed;
  if (data.is_blocked === true){
    err('ACCOUNT BLOCKED: is_blocked = true');
    process.exit(1);
  }
  if (data.is_locked === true){
    err('ACCOUNT LOCKED: is_locked = true');
    process.exit(1);
  }

  sid = data.session_id;
  ticket = data.socket_ticket;
  const frameKeyB64 = data.frame_key;
  if (!sid || !frameKeyB64){
    err('bad session payload');
    console.dir(data, { depth: 3 });
    process.exit(1);
  }
  frameKeyBuf = importFrameKey(frameKeyB64);

  log('session       :', sid);
  log('plays_remaining:', data.plays_remaining);
  log('live_mode     :', !!data.live_mode);
  log('drip_mode     :', !!data.drip_mode);

  ws = new WebSocket(CFG.WS_URL, {
    headers: {
      'Cookie':           cookie,
      'Origin':           CFG.ORIGIN,
      'User-Agent':       CFG.USER_AGENT,
      'Accept-Language':  'en-US,en;q=0.9'
    }
  });

  ws.on('open', () => {
    log('ws open');
    sendSigned('hello', { session_id: sid, ticket, resume_from_seq: 0 });
  });
  ws.on('message', data => {
    try { onFrame(typeof data === 'string' ? data : data.toString()); }
    catch (e){ err('onFrame threw', e); }
  });
  ws.on('close', (code, reason) => {
    log('ws closed code=' + code + ' reason=' + reason.toString());
    if (!sessionEnded) stopped = true;
    process.exit(0);
  });
  ws.on('error', e => err('ws error', e.message));
}

// ============================================================
// INPUT HANDLING
// ============================================================
function parseArgs(){
  const args = process.argv.slice(2);
  let cookieArg = null;
  for (let i = 0; i < args.length; i++){
    if (args[i] === '--cookie' && args[i+1]) cookieArg = args[++i];
    else if (!cookieArg && !args[i].startsWith('--')) cookieArg = args[i];
  }
  return cookieArg;
}

async function main(){
  const inline = parseArgs();
  if (inline){
    cookie = inline.trim();
    return run();
  }
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  rl.question('Paste cookie string from Cookie-Editor:\n> ', ans => {
    rl.close();
    cookie = ans.trim();
    if (!cookie){ err('no cookie provided'); process.exit(1); }
    run().catch(e => { err(e); process.exit(1); });
  });
}

process.on('SIGINT', () => {
  log('SIGINT · killing');
  try { ws && ws.close(); } catch {}
  process.exit(0);
});

log('TT Direct — Node.js edition');
main().catch(e => { err(e); process.exit(1); });