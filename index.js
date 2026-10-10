/**
 * ws4channels - WeatherStar 4000 HLS Stream
 * Captures the ws4kp weather simulator via Puppeteer and transcodes it
 * to an HLS stream using FFmpeg. Serves the playlist and segments via
 * Express.
 */

import puppeteer from 'puppeteer';
import express from 'express';
import ffmpeg from 'fluent-ffmpeg';
import path from 'path';
import fs from 'fs';
import os from 'os';
import Xvfb from 'xvfb';
import { PassThrough, Writable } from 'stream';
import { spawn } from 'child_process';

process.setMaxListeners(50);

const app = express();
const __dirname = path.dirname(new URL(import.meta.url).pathname);
const VERSION = 'vAPP_VERSION';

// ── Configuration ────────────────────────────────────────────────────────

const ZIP_CODE = (process.env.ZIP_CODE || '90210').split(',').map(z => z.trim());
const WS4KP_HOST = process.env.WS4KP_HOST || 'localhost';
const WS4KP_PORT = process.env.WS4KP_PORT || '8080';
const STREAM_PORT = process.env.STREAM_PORT || '9798';
const WS4KP_FORECAST_CD = process.env.WS4KP_FORECAST_CD || '1.0';
const WS4KP_SCANLINES = process.env.WS4KP_SCANLINES.toLowerCase() === 'true' || 'false';
const WS4KP_CURRENT_WEATHER = process.env.WS4KP_CURRENT_WEATHER?.toLowerCase() === 'true' || 'true';
const WS4KP_LATEST_OBSERVATIONS = process.env.WS4KP_LATEST_OBSERVATIONS?.toLowerCase() === 'true' || 'true';
const WS4KP_HOURLY = process.env.WS4KP_HOURLY?.toLowerCase() === 'true' || 'true';
const WS4KP_HOURLY_GRAPH = process.env.WS4KP_HOURLY_GRAPH?.toLowerCase() === 'true' || 'false';
const WS4KP_TRAVEL = process.env.WS4KP_TRAVEL?.toLowerCase() === 'true' || 'false';
const WS4KP_REGIONAL_FORECAST = process.env.WS4KP_REGIONAL_FORECAST === 'true' || 'false';
const WS4KP_LOCAL_FORECAST = process.env.WS4KP_LOCAL_FORECAST?.toLowerCase() === 'true' || 'true';
const WS4KP_EXTENDED_FORECAST = process.env.WS4KP_EXTENDED_FORECAST?.toLowerCase() === 'true' || 'true';
const WS4KP_ALMANAC = process.env.WS4KP_ALMANAC?.toLowerCase() === 'true' || 'false';
const WS4KP_RADAR = process.env.WS4KP_RADAR?.toLowerCase() === 'true' || 'true';
const WS4KP_URL = `http://${WS4KP_HOST}:${WS4KP_PORT}?radar=${WS4KP_RADAR}&almanac=${WS4KP_ALMANAC}&extended-forecast=${WS4KP_EXTENDED_FORECAST}&local-forecast=${WS4KP_LOCAL_FORECAST}&regional-forecast=${WS4KP_REGIONAL_FORECAST}&travel=${WS4KP_TRAVEL}&hourly-graph=${WS4KP_HOURLY_GRAPH}&hourly=${WS4KP_HOURLY}&latest-observations=${WS4KP_LATEST_OBSERVATIONS}&current-weather=${WS4KP_CURRENT_WEATHER}&scanLines=${WS4KP_SCANLINES}&speed=${WS4KP_FORECAST_CD}&spc-outlook=false`;
const PERMALINK_URL = process.env.PERMALINK_URL || null;
const KBPS_BITRATE = process.env.KBPS_BITRATE || '1000';
const FRAME_RATE = Number(process.env.FRAME_RATE) || 15;
const SHUFFLE_MUSIC = process.env.SHUFFLE_MUSIC?.toLowerCase() === 'true' || false;
const SHOW_SONG_TITLE = process.env.SHOW_SONG_TITLE?.toLowerCase() === 'true' || false;
const HLS_SEGMENT_SECONDS = 2;
const sleep = (ms) => new Promise(resolve => setTimeout(resolve, ms));

/** Minutes between forced browser restarts. 0 = disabled. */
const BROWSER_REFRESH_MINUTES = parseInt(process.env.BROWSER_REFRESH_MINUTES || '0');

/** Segment freshness watchdog thresholds */
const SEGMENT_STALL_WARN_MS = 8000;
const SEGMENT_CHECK_INTERVAL_MS = 2000;
const STDERR_BUFFER_LINES = 40;

/** Song title polling interval (ms) */
const SONG_TITLE_POLL_INTERVAL_MS = 1000;

// ── Directories ──────────────────────────────────────────────────────────

const OUTPUT_DIR = path.join('/tmp', 'output');
const AUDIO_DIR = path.join(__dirname, 'music');
const LOGO_DIR = path.join(__dirname, 'logo');
const HLS_FILE = path.join(OUTPUT_DIR, 'stream.m3u8');

[OUTPUT_DIR, AUDIO_DIR, LOGO_DIR].forEach(dir => {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir);
});

// ── View mode configuration ──────────────────────────────────────────────

const validViewModes = ['standard', 'wide', 'wide-enhanced', 'portrait-enhanced'];
const VIEW_MODE = validViewModes.includes((process.env.VIEW_MODE || 'wide').toLowerCase())
  ? (process.env.VIEW_MODE || 'wide').toLowerCase()
  : 'wide';

const VIEW_DIMENSIONS = (() => {
  switch (VIEW_MODE) {
    case 'standard':          return { width: 640,  height: 480 };
    case 'portrait-enhanced': return { width: 720,  height: 1280 };
    case 'wide':
    case 'wide-enhanced':
    default:                  return { width: 1280, height: 720 };
  }
})();

// ── Process state ────────────────────────────────────────────────────────

let ffmpegProc = null;
let hlsWatcher = null;
let browser = null;
let page = null;
let captureProcess = null;
let captureInterval = null;
let refreshTimer = null;
let segmentWatchdogInterval = null;
let songTitlePollingInterval = null;
let isStreamReady = false;
let xvfb = null;
let lastLoggedTime = null;
let songNowPlaying = 'Starting stream...';
let songWasPlaying = 'Starting stream...';
let currentZipIndex = 0;
let zipRotationTimeout = null;

/** Backpressure / overlap protection */
let isCapturing = false;
let isRestartingBrowser = false;
let browserRestartCount = 0;
let framesSkippedRestarting = 0;

/** Frame timing stats */
let totalFrameTimeMs = 0;
let maxFrameTimeMs = 0;
let avgFrameTimeMs = 0;
let captureStartedAt = null;

/** ffmpeg diagnostics */
let stderrBuffer = [];
let lastProgress = null;
let lastProgressAt = null;
let lastSegmentMtimeMs = null;
let lastSegmentChangeAt = null;
let segmentStallActive = false;
let segmentStallWarningsIssued = 0;
let lastStallDumpAt = 0;

/** Idle stream management */
let streamActive = false;
let streamGraceTimer = null;
const STREAM_GRACE_PERIOD_S = 30; // Grace period before pausing idle streams

const waitFor = ms => new Promise(resolve => setTimeout(resolve, ms));

// ── Helpers ──────────────────────────────────────────────────────────────

function logTS(msg) {
  console.log(`[${new Date().toISOString()}] ${msg}`);
}

function shuffleArray(array) {
  const arr = array.slice();
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function clearOutputDir() {
  try {
    for (const file of fs.readdirSync(OUTPUT_DIR)) {
      fs.unlinkSync(path.join(OUTPUT_DIR, file));
    }
    logTS('Cleaned up stale HLS files.');
  } catch (err) {
    logTS(`Warning: Could not clear output dir: ${err.message}`);
  }
}

function getContainerLimits() {
  let cpuQuotaPath = '/sys/fs/cgroup/cpu.max';
  let memLimitPath = '/sys/fs/cgroup/memory.max';
  let cpus = os.cpus().length;
  let memory = os.totalmem();
  try {
    const [quota, period] = fs.readFileSync(cpuQuotaPath, 'utf8').trim().split(' ');
    if (quota !== 'max') cpus = parseFloat((parseInt(quota) / parseInt(period)).toFixed(2));
  } catch {}
  try {
    const raw = fs.readFileSync(memLimitPath, 'utf8').trim();
    if (raw !== 'max') memory = parseInt(raw);
  } catch {}
  return { cpus, memoryMB: Math.round(memory / (1024 * 1024)) };
}

// ── Music ────────────────────────────────────────────────────────────────

function createAudioInputFile() {
  const defaultMp3s = [
    '01 Weatherscan Track 26.mp3','02 Weatherscan Track 3.mp3','03 Tropical Breeze.mp3',
    '04 Late Nite Cafe.mp3','05 Care Free.mp3','06 Weatherscan Track 14.mp3','07 Weatherscan Track 18.mp3'
  ];
  const supportedExtensions = ['.mp3', '.m4a', '.aac', '.wav', '.flac', '.ogg'];

  let files = [];
  try {
    files = fs.readdirSync(AUDIO_DIR).filter(f =>
      supportedExtensions.some(ext => f.toLowerCase().endsWith(ext))
    );
    if (!files.length) {
      console.warn('No supported audio files found; using default music list');
      files = defaultMp3s;
    }
  } catch (err) {
    console.error(`Failed to read music dir: ${err.message}`);
    files = defaultMp3s;
  }

  if (SHUFFLE_MUSIC) {
    files = shuffleArray(files);
    logTS('Shuffled music list.');
  }

  logTS(`Loaded ${files.length} music file(s).`);

  const audioList = files.map(f => `file '${path.join(AUDIO_DIR, f)}'`).join('\n');
  fs.writeFileSync(path.join(__dirname, 'audio_list.txt'), audioList);
}

// ── XMLTV guide ──────────────────────────────────────────────────────────

function generateXMLTV(host) {
  const now = new Date();
  const baseUrl = `http://${host}`;
  let xml = `<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE tv SYSTEM "xmltv.dtd">
<tv>
  <channel id="WS4000">
    <display-name>WeatherStar 4000</display-name>
    <icon src="${baseUrl}/logo/ws4000.png"/>
  </channel>`;

  for (let i = 0; i < 24; i++) {
    const startTime = new Date(now.getTime() + i * 3600 * 1000);
    const endTime = new Date(startTime.getTime() + 3600 * 1000);
    const pad = (n) => String(n).padStart(2, '0');
    const start = `${startTime.getFullYear()}${pad(startTime.getMonth()+1)}${pad(startTime.getDate())}${pad(startTime.getHours())}${pad(startTime.getMinutes())}${pad(startTime.getSeconds())} +0000`;
    const end = `${endTime.getFullYear()}${pad(endTime.getMonth()+1)}${pad(endTime.getDate())}${pad(endTime.getHours())}${pad(endTime.getMinutes())}${pad(endTime.getSeconds())} +0000`;
    xml += `
  <programme start="${start}" stop="${end}" channel="WS4000">
    <title lang="en">Local Weather</title>
    <desc lang="en">Enjoy your local weather with a touch of nostalgia.</desc>
    <icon src="${baseUrl}/logo/ws4000.png"/>
  </programme>`;
  }

  xml += '</tv>';
  return xml;
}

// ── Song title polling ───────────────────────────────────────────────────

async function startSongTitlePolling() {
  if (songTitlePollingInterval) clearInterval(songTitlePollingInterval);
  if (!SHOW_SONG_TITLE || !page || page.isClosed()) return;

  logTS('Starting song title polling');
  songTitlePollingInterval = setInterval(async () => {
    if (!page || page.isClosed()) {
      clearInterval(songTitlePollingInterval);
      songTitlePollingInterval = null;
      return;
    }

    if (songNowPlaying !== songWasPlaying) {
      logTS(`🎵 Song changed: "${songWasPlaying}" → "${songNowPlaying}"`);
      try {
        await page.evaluate((songName) => {
          const checkbox = document.querySelector('#settings-customTextEnable-checkbox');
          const textInput = document.querySelector('#settings-customText-string');
          const setButton = document.querySelector('#settings-customText-button');

          if (checkbox) { checkbox.checked = true; checkbox.dispatchEvent(new Event('change', { bubbles: true })); }
          if (textInput) {
            textInput.value = 'Now Playing: ' + songName;
            textInput.dispatchEvent(new Event('input', { bubbles: true }));
            textInput.dispatchEvent(new Event('change', { bubbles: true }));
          }
          if (setButton) setButton.click();
        }, songNowPlaying);
        songWasPlaying = songNowPlaying;
      } catch (err) {
        logTS(`Failed to update custom text: ${err.message}`);
      }
    }
  }, SONG_TITLE_POLL_INTERVAL_MS);
}

function stopSongTitlePolling() {
  if (songTitlePollingInterval) {
    clearInterval(songTitlePollingInterval);
    songTitlePollingInterval = null;
    logTS('Song title polling stopped');
  }
}

// ── ZIP code rotation ────────────────────────────────────────────────────

async function rotateZipCode() {
  if (!page || page.isClosed() || !ZIP_CODE || ZIP_CODE.length <= 1) return;

  currentZipIndex = (currentZipIndex + 1) % ZIP_CODE.length;
  const nextZip = ZIP_CODE[currentZipIndex];

  try {
    logTS(`🔄 Rotating location to: ${nextZip}`);

    await page.evaluate((zip) => {
      const input = document.querySelector('#txtLocation');
      if (input) {
        input.value = zip;
        input.dispatchEvent(new Event('input', { bubbles: true }));
        input.dispatchEvent(new Event('change', { bubbles: true }));
      }
    }, nextZip);

    const submitButton = await page.$('#btnGetLatLng');
    if (submitButton) {
      await submitButton.evaluate(el => el.click());
    } else {
      await page.keyboard.press('Enter');
    }

    await sleep(5000);
    logTS(`✅ Location rotation to ${nextZip} complete.`);
  } catch (err) {
    logTS(`❌ Failed to rotate ZIP code: ${err.message}`);
  }
}

function getMsUntilNext8MinWindow() {
  const now = new Date();
  const currentMinutes = now.getMinutes();
  let targetMinutes = (Math.floor(currentMinutes / 10) * 10) + 8;

  if (currentMinutes >= targetMinutes) targetMinutes += 10;

  const targetDate = new Date(now);
  targetDate.setMinutes(targetMinutes);
  targetDate.setSeconds(0);
  targetDate.setMilliseconds(0);

  if (targetDate <= now) targetDate.setHours(targetDate.getHours() + 1);

  return targetDate.getTime() - now.getTime() + 500;
}

async function startZipRotation() {
  if (zipRotationTimeout) clearTimeout(zipRotationTimeout);

  const delay = getMsUntilNext8MinWindow();
  const targetDate = new Date(Date.now() + delay);
  logTS(`⏰ Next ZIP rotation in ${Math.round(delay / 1000)}s (at ${targetDate.toLocaleTimeString()})`);

  zipRotationTimeout = setTimeout(async () => {
    try { await rotateZipCode(); } catch (err) { logTS(`❌ Rotation error: ${err.message}`); }
    finally { startZipRotation(); }
  }, delay);
}

// ── Browser management ───────────────────────────────────────────────────

async function startBrowser(reason = 'initial startup') {
  if (isRestartingBrowser) {
    logTS('Ignoring duplicate startBrowser() call — restart already in progress');
    return;
  }
  isRestartingBrowser = true;

  try {
    stopSongTitlePolling();
    browserRestartCount++;

    if (xvfb) await xvfb.stop();
    xvfb = await new Xvfb({
      silent: false,
      reuse: false,
      xvfb_args: ['-screen', '0', `${VIEW_DIMENSIONS.width}x${VIEW_DIMENSIONS.height}x24 -ac`],
    });
    await xvfb.start();
    process.env['DISPLAY'] = xvfb._display;
    logTS(`Xvfb launched (display ${process.env.DISPLAY})`);
    await sleep(3000);

    logTS(`Launching browser (launch #${browserRestartCount}, reason: ${reason})`);
    if (browser) await browser.close().catch(() => {});

    browser = await puppeteer.launch({
      headless: false,
      args: [
        '--no-sandbox',
        '--disable-setuid-sandbox',
        '--disable-infobars',
        '--ignore-certificate-errors',
        `--window-size=${VIEW_DIMENSIONS.width},${VIEW_DIMENSIONS.height}`,
        '--disable-dev-shm-usage',
        '--disable-extensions',
        '--start-fullscreen',
        '--autoplay-policy=no-user-gesture-required',
        `--display=${xvfb._display}`,
      ],
      defaultViewport: null,
    });

    page = await browser.newPage();

    if (PERMALINK_URL) {
      logTS(`Using permalink: ${PERMALINK_URL}`);
      await page.goto(PERMALINK_URL, { waitUntil: 'networkidle2', timeout: 30000 });
    } else {
      logTS(`Using URL: ${WS4KP_URL}`);
      await page.goto(WS4KP_URL, { waitUntil: 'networkidle2', timeout: 30000 });

      // Auto-fill ZIP code
      try {
        const zipInput = await page.waitForSelector('input[placeholder="Zip or City, State"], input', { timeout: 5000 });
        if (zipInput) {
          await zipInput.type(ZIP_CODE[currentZipIndex], { delay: 100 });
          await page.waitForSelector('#divQuery .autocomplete-suggestions .suggestion');
          await page.keyboard.press('ArrowDown');
          await page.waitForSelector('#divQuery .autocomplete-suggestions .suggestion.selected');
          const goButton = await page.$('button[type="submit"]');
          if (goButton) await goButton.click();
          else await zipInput.press('Enter');
          await page.waitForSelector('div.weather-display, #weather-content', { timeout: 30000 });
        }
      } catch {}

      // Set view mode
      try {
        // ws4kp 6.x (classic) — wide checkbox
        const widescreenCheckbox = await page.waitForSelector('#settings-wide-checkbox', { timeout: 100 });
        const widescreenChecked = await widescreenCheckbox.evaluate(el => el.checked);

        if (VIEW_MODE === 'wide-enhanced' || VIEW_MODE === 'portrait-enhanced') {
          console.error('This version of ws4kp only supports standard/wide VIEW_MODE');
          await browser.close();
          await xvfb.stop();
          process.exit(1);
        }

        if ((widescreenChecked && VIEW_MODE === 'standard') || (!widescreenChecked && VIEW_MODE === 'wide')) {
          await widescreenCheckbox.click();
        }
      } catch {
        try {
          // ws4kp 7.x — view mode dropdown
          const viewSelector = await page.waitForSelector('#settings-viewMode-select');
          await viewSelector.evaluate((el, mode) => { el.value = mode; el.dispatchEvent(new Event('change')); }, VIEW_MODE);
        } catch {}
      }

      // Enable kiosk mode
      const kioskCheckbox = await page.waitForSelector('#settings-kiosk-checkbox');
      const kioskChecked = await kioskCheckbox.evaluate(el => el.checked);
      if (!kioskChecked) await kioskCheckbox.click();
    }

    await page.setViewport({ ...VIEW_DIMENSIONS });
    isCapturing = false;
    captureStartedAt = null;

    if (SHOW_SONG_TITLE) await startSongTitlePolling();
    logTS(`Browser ready (launch #${browserRestartCount})`);
  } finally {
    isRestartingBrowser = false;
  }
}

function scheduleBrowserRefresh() {
  if (refreshTimer) clearInterval(refreshTimer);
  if (!BROWSER_REFRESH_MINUTES || BROWSER_REFRESH_MINUTES <= 0) {
    logTS('Scheduled browser refresh disabled');
    return;
  }
  logTS(`Scheduled browser refresh: every ${BROWSER_REFRESH_MINUTES} minute(s)`);
  refreshTimer = setInterval(async () => {
    try {
      logTS('Restarting transcoding after scheduled browser refresh');
      await stopTranscoding();
      await startTranscoding();
    } catch (err) {
      console.error(`Scheduled refresh failed: ${err.message}`);
    }
  }, BROWSER_REFRESH_MINUTES * 60 * 1000);
}

// ── FFmpeg diagnostics ───────────────────────────────────────────────────

function dumpFfmpegDiagnostics(gapMs) {
  logTS(`FFMPEG STALL: no segment activity in ${gapMs}ms (expected ~${HLS_SEGMENT_SECONDS * 1000}ms intervals)`);

  if (lastProgress) {
    const since = lastProgressAt ? (Date.now() - lastProgressAt) : null;
    const { frames, currentFps, currentKbps, timemark } = lastProgress;
    logTS(`Last progress (${since}ms ago): frames=${frames}, fps=${currentFps}, kbps=${currentKbps}, timemark=${timemark}`);
  } else {
    logTS('No ffmpeg progress events yet');
  }

  if (stderrBuffer.length) {
    logTS(`Last ${stderrBuffer.length} stderr line(s):`);
    stderrBuffer.forEach(line => logTS(`  ffmpeg: ${line}`));
  } else {
    logTS('(no ffmpeg stderr captured)');
  }
}

function startSegmentWatchdog() {
  if (segmentWatchdogInterval) clearInterval(segmentWatchdogInterval);
  lastSegmentMtimeMs = null;
  lastSegmentChangeAt = Date.now();
  segmentStallActive = false;

  segmentWatchdogInterval = setInterval(() => {
    let files;
    try { files = fs.readdirSync(OUTPUT_DIR); } catch { return; }

    let newestMtime = 0;
    for (const f of files) {
      if (!f.endsWith('.ts') && !f.endsWith('.m3u8')) continue;
      try {
        const stat = fs.statSync(path.join(OUTPUT_DIR, f));
        if (stat.mtimeMs > newestMtime) newestMtime = stat.mtimeMs;
      } catch {}
    }

    if (newestMtime > 0 && (lastSegmentMtimeMs === null || newestMtime > lastSegmentMtimeMs)) {
      lastSegmentMtimeMs = newestMtime;
      lastSegmentChangeAt = Date.now();
      if (segmentStallActive) {
        logTS('FFMPEG STALL RECOVERED: output flowing again');
        segmentStallActive = false;
      }
      return;
    }

    const gapMs = Date.now() - lastSegmentChangeAt;
    if (gapMs > SEGMENT_STALL_WARN_MS) {
      if (!segmentStallActive || Date.now() - lastStallDumpAt > 5000) {
        segmentStallActive = true;
        lastStallDumpAt = Date.now();
        segmentStallWarningsIssued++;
        dumpFfmpegDiagnostics(gapMs);
      }
    }
  }, SEGMENT_CHECK_INTERVAL_MS);
}

// ── Transcoding ──────────────────────────────────────────────────────────

async function ensureFfmpeg() {
  if (ffmpegProc) return;

  logTS('Starting ffmpeg and capture loop...');

  // Frame capture interval
  captureInterval = setInterval(async () => {
    if (!ffmpegProc || !page || isRestartingBrowser) return;

    if (page.isClosed()) {
      await startBrowser('page was closed');
      return;
    }
  }, 1000 / FRAME_RATE);

  // FFmpeg process
  ffmpegProc = ffmpeg()
    .input(xvfb._display + '.0')
    .inputOptions(['-f x11grab', `-framerate ${FRAME_RATE}`])
    .input(path.join(__dirname, 'audio_list.txt'))
    .inputOptions(['-f concat', '-safe 0', '-stream_loop -1', '-loglevel debug'])
    .complexFilter([
      `[0:v]scale=${VIEW_DIMENSIONS.width}:${VIEW_DIMENSIONS.height}[v]`,
      '[1:a]aresample=48000,volume=0.5[a]',
    ])
    .outputOptions([
      '-map [v]', '-map [a]',
      '-c:v libx264', '-preset veryfast',
      '-c:a aac', '-b:a 128k',
      '-rc_mode 2', `-g ${FRAME_RATE * HLS_SEGMENT_SECONDS}`,
      `-b:v ${KBPS_BITRATE}k`,
      '-f hls', `-hls_time ${HLS_SEGMENT_SECONDS}`,
      '-hls_list_size 6', '-hls_flags delete_segments',
    ])
    .output(HLS_FILE)
    .on('start', (cmd) => {
      logTS(`Started FFmpeg: ${cmd}`);
      isStreamReady = true;
      isCapturing = true;
      captureStartedAt = Date.now();

      if (!hlsWatcher && !fs.existsSync(HLS_FILE)) {
        logTS('Waiting for HLS playlist...');
        hlsWatcher = fs.watch(OUTPUT_DIR, (eventType, filename) => {
          if (filename === 'stream.m3u8') {
            logTS('HLS playlist detected');
            isStreamReady = true;
            captureStartedAt = Date.now();
            hlsWatcher?.close();
            hlsWatcher = null;
          }
        });
      }
    })
    .on('stderr', (line) => {
      stderrBuffer.push(line);
      if (stderrBuffer.length > STDERR_BUFFER_LINES) stderrBuffer.shift();

      // Skip file-open messages for HLS output
      if (line.includes('for writing')) return;

      // Track current song title from ffmpeg input log
      const songMatch = line.match(/Opening '([^']+?)'/);
      if (songMatch && songMatch[1].match(/\.(mp3|m4a|aac|wav|flac|ogg)$/i)) {
        songNowPlaying = path.parse(songMatch[1]).name;
      }
    })
    .on('progress', (p) => {
      lastProgress = p;
      lastProgressAt = Date.now();

      if (captureStartedAt) {
        totalFrameTimeMs = Date.now() - captureStartedAt;
        const avg = lastProgress.frames > 0
          ? Math.round(totalFrameTimeMs / lastProgress.frames)
          : null;
        avgFrameTimeMs = avg;
        if (avg > maxFrameTimeMs) maxFrameTimeMs = avg;
      }

      const elapsed = Math.floor(totalFrameTimeMs / 1000);
      if (elapsed % 60 === 0 && lastLoggedTime !== elapsed) {
        lastLoggedTime = elapsed;
        logTS(`Health: frames=${lastProgress.frames}, avg=${avgFrameTimeMs}ms, max=${maxFrameTimeMs}ms`);
      }
    })
    .on('error', async (err) => {
      logTS(`FFmpeg error: ${err.message}`);
      if (streamActive) {
        await stopFfmpeg();
        ensureFfmpeg();
      }
    })
    .on('end', () => {
      ffmpegProc = null;
      isStreamReady = false;
      isCapturing = false;
      captureStartedAt = null;
    });

  startSegmentWatchdog();
  ffmpegProc.run();
}

async function stopFfmpeg() {
  logTS('Stopping ffmpeg...');

  if (captureInterval) { clearInterval(captureInterval); captureInterval = null; }
  if (ffmpegProc) {
    ffmpegProc.kill('SIGINT');
    ffmpegProc = null;
    await sleep(1000);
  }
  if (segmentWatchdogInterval) { clearInterval(segmentWatchdogInterval); segmentWatchdogInterval = null; }
  if (hlsWatcher) { hlsWatcher.close(); hlsWatcher = null; }

  isStreamReady = false;
  isCapturing = false;
  captureStartedAt = null;
  lastProgress = lastProgressAt = lastSegmentChangeAt = null;
  clearOutputDir();
}

async function startTranscoding() {
  await startBrowser('initial startup');
  scheduleBrowserRefresh();
}

async function stopTranscoding() {
  stopSongTitlePolling();
  if (refreshTimer) { clearInterval(refreshTimer); refreshTimer = null; }
  if (zipRotationTimeout) { clearTimeout(zipRotationTimeout); zipRotationTimeout = null; }
  await stopFfmpeg();
}

// ── Express routes ───────────────────────────────────────────────────────

app.get('/playlist.m3u', (req, res) => {
  const host = req.headers.host || `localhost:${STREAM_PORT}`;
  const baseUrl = `http://${host}`;
  res.set('Content-Type', 'application/x-mpegURL');
  res.send(`#EXTM3U
#EXTINF:-1 channel-id="weatherStar4000" tvg-id="weatherStar4000" tvg-channel-no="275" tvc-guide-placeholders="3600" tvc-guide-title="Local Weather" tvc-guide-description="Enjoy your local weather with a touch of nostalgia." tvc-guide-art="${baseUrl}/logo/ws4000.png" tvg-logo="${baseUrl}/logo/ws4000.png",WeatherStar 4000
${baseUrl}/stream/stream.m3u8
`);
});

app.get('/guide.xml', (req, res) => {
  const host = req.headers.host || `localhost:${STREAM_PORT}`;
  res.set('Content-Type', 'application/xml');
  res.send(generateXMLTV(host));
});

app.get('/health', (req, res) => {
  const frames = lastProgress?.frames ?? null;
  const currentFps = lastProgress?.currentFps ?? null;
  const lastFfmpegTimemark = lastProgress?.timemark ?? null;

  res.status(isStreamReady ? 200 : 503).json({
    ready: isStreamReady,
    lastFfmpegTimemark,
    currentFps,
    totalFrameTimeMs,
    frames,
    avgFrameTimeMs,
    maxFrameTimeMs,
    msSinceLastSegmentChange: lastSegmentChangeAt ? Date.now() - lastSegmentChangeAt : null,
    msSinceLastFfmpegProgress: lastProgressAt ? Date.now() - lastProgressAt : null,
    segmentStallActive,
    segmentStallWarningsIssued,
    browserRestartCount,
    framesSkippedRestarting,
  });
});

// ── Stream endpoint with idle management ─────────────────────────────────

app.use('/stream', async (req, res, next) => {
  if (!req.url.endsWith('stream.m3u8')) return next();

  if (!streamActive) {
    streamActive = true;
    logTS('📡 Client connected — starting ffmpeg');
    ensureFfmpeg();
  }

  // Reset grace timer on every request
  clearTimeout(streamGraceTimer);
  streamGraceTimer = setTimeout(async () => {
    streamActive = false;
    logTS('⏳ No requests during grace period — pausing ffmpeg');
    await stopFfmpeg();
  }, STREAM_GRACE_PERIOD_S * 1000);

  // Wait for stream readiness
  let attempts = 0;
  const maxAttempts = 30;
  while (!isStreamReady && attempts < maxAttempts) {
    await sleep(500);
    attempts++;
    if (attempts % 5 === 0) logTS(`Warming up... (${attempts * 500}ms)`);
  }

  if (!isStreamReady) {
    logTS('❌ Timeout waiting for stream readiness');
    return res.status(503).send('Stream is warming up. Please retry.');
  }

  next();
});

app.use('/stream', express.static(OUTPUT_DIR));
app.use('/logo', express.static(LOGO_DIR));

// ── Boot ─────────────────────────────────────────────────────────────────

const { cpus, memoryMB } = getContainerLimits();
logTS(`ws4channels ${VERSION} — ${cpus} CPU, ${memoryMB}MB RAM`);
createAudioInputFile();
logTS(`Streaming on port ${STREAM_PORT}`);
logTS('Idle — ffmpeg starts on first client connection');

if (ZIP_CODE.length > 1) startZipRotation();

app.listen(STREAM_PORT, async () => {
  await startTranscoding();
});

process.on('SIGINT',  async () => { logTS('SIGINT received'); await stopTranscoding(); process.exit(); });
process.on('SIGTERM', async () => { logTS('SIGTERM received'); await stopTranscoding(); process.exit(); });
