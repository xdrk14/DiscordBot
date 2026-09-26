require('dotenv').config();
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const express = require('express');
const {
  Client, GatewayIntentBits, Partials, REST, Routes, SlashCommandBuilder, ChannelType,
} = require('discord.js');
const session = require('express-session');
const {
  joinVoiceChannel,
  getVoiceConnection,
  createAudioPlayer,
  createAudioResource,
  entersState,
  VoiceConnectionStatus,
  AudioPlayerStatus,
  StreamType,
} = require('@discordjs/voice');
const { Readable } = require('stream');
const googleTTS = require('google-tts-api');
const multer = require('multer');
const { execFile } = require('child_process');
const { promisify } = require('util');
const ffmpegPath = require('ffmpeg-static');
const prism = require('prism-media');

const execFileAsync = promisify(execFile);

const CONFIG_PATH = path.join(__dirname, 'config.json');
const SOUNDS_DIR = path.join(__dirname, 'sounds');
const PORT = process.env.PORT || 3000;
const PUBLIC_URL = (process.env.PUBLIC_URL || `http://localhost:${PORT}`).replace(/\/$/, '');
const SOUND_EXTENSIONS = ['.mp3', '.wav', '.ogg', '.m4a'];
// EBU R128 loudness target: hearable/audible without screeching peaks or clipping.
const LOUDNESS_FILTER = 'loudnorm=I=-16:TP=-1.5:LRA=11';

// Dashboard login: if no real password is configured, generate one per boot rather than
// ever running with an open/default one. Print it once so a fresh setup isn't locked out.
let DASHBOARD_PASSWORD = process.env.DASHBOARD_PASSWORD;
if (!DASHBOARD_PASSWORD || DASHBOARD_PASSWORD === 'changeme123') {
  DASHBOARD_PASSWORD = crypto.randomBytes(9).toString('base64url');
  console.log('\n==============================================');
  console.log('No DASHBOARD_PASSWORD set in .env - generated one for this run:');
  console.log(`  ${DASHBOARD_PASSWORD}`);
  console.log('Set DASHBOARD_PASSWORD in .env to keep it stable across restarts.');
  console.log('==============================================\n');
}

const SESSION_SECRET = process.env.SESSION_SECRET && process.env.SESSION_SECRET !== 'change-this-to-a-long-random-string'
  ? process.env.SESSION_SECRET
  : crypto.randomBytes(32).toString('hex'); // regenerated each boot if not set - fine, just means old sessions won't survive a restart

// one-time login tokens issued by the /dashboard slash command
const dashboardTokens = new Map(); // token -> expiresAt
function issueDashboardToken() {
  const token = crypto.randomBytes(24).toString('hex');
  dashboardTokens.set(token, Date.now() + 10 * 60 * 1000);
  return token;
}
function consumeDashboardToken(token) {
  const expires = dashboardTokens.get(token);
  dashboardTokens.delete(token);
  return !!expires && expires > Date.now();
}

if (!fs.existsSync(SOUNDS_DIR)) fs.mkdirSync(SOUNDS_DIR);
const DIGIT_WORDS = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine'];

// Google Translate TTS language codes (used by google-tts-api's `lang` option)
const TTS_LANGS = [
  'en', 'en-US', 'en-GB', 'en-AU', 'en-IN',
  'es', 'es-ES', 'fr', 'fr-FR', 'de', 'it', 'pt', 'pt-BR', 'ru', 'ja', 'ko',
  'zh-CN', 'zh-TW', 'ar', 'hi', 'nl', 'pl', 'tr', 'vi', 'th', 'id', 'sv', 'el', 'ro', 'cy',
];

function randomDigit() {
  return Math.floor(Math.random() * 10);
}
function randomDigitWord() {
  return DIGIT_WORDS[randomDigit()];
}

// ---------- persisted config ----------
function normalizeRule(r) {
  return {
    id: (r && r.id) || crypto.randomUUID(),
    name: r && typeof r.name === 'string' && r.name.trim() ? r.name.trim() : 'Unnamed rule',
    enabled: !!(r && r.enabled),
    targetUserId: (r && typeof r.targetUserId === 'string') ? r.targetUserId : '',
    triggerType: ['number', 'any', 'contains'].includes(r && r.triggerType) ? r.triggerType : 'number',
    triggerKeyword: (r && typeof r.triggerKeyword === 'string') ? r.triggerKeyword : '',
    channelId: (r && typeof r.channelId === 'string') ? r.channelId : '',
    replyType: ['digit', 'text', 'tts', 'voice', 'soundboardAttachment', 'soundboardVoice'].includes(r && r.replyType) ? r.replyType : 'digit',
    replyText: (r && typeof r.replyText === 'string') ? r.replyText : '',
    ttsLang: TTS_LANGS.includes(r && r.ttsLang) ? r.ttsLang : 'en',
    ttsSlow: !!(r && r.ttsSlow),
    soundId: (r && typeof r.soundId === 'string') ? r.soundId : '',
    voiceChannelId: (r && typeof r.voiceChannelId === 'string') ? r.voiceChannelId : '',
  };
}

function migrateConfig(raw) {
  if (raw && Array.isArray(raw.rules)) {
    return { enabled: !!raw.enabled, rules: raw.rules.map(normalizeRule) };
  }
  // legacy single-rule flat shape
  if (raw && (raw.targetUserId !== undefined || raw.triggerType !== undefined)) {
    const rule = normalizeRule({
      name: 'Migrated rule',
      enabled: true,
      targetUserId: raw.targetUserId || '',
      triggerType: raw.triggerType || 'number',
      triggerKeyword: raw.triggerKeyword || '',
      channelId: raw.channelId || '',
      replyType: 'text',
      replyText: raw.customReply || '',
    });
    return { enabled: !!raw.enabled, rules: [rule] };
  }
  return { enabled: false, rules: [] };
}

function loadConfig() {
  if (fs.existsSync(CONFIG_PATH)) {
    try {
      return migrateConfig(JSON.parse(fs.readFileSync(CONFIG_PATH, 'utf8')));
    } catch {
      // fall through to default
    }
  }
  return { enabled: false, rules: [] };
}
function saveConfig(cfg) {
  fs.writeFileSync(CONFIG_PATH, JSON.stringify(cfg, null, 2));
}
let config = loadConfig();

// keep a short in-memory log the dashboard can poll
const log = [];
function addLog(line) {
  log.unshift(`[${new Date().toLocaleTimeString()}] ${line}`);
  if (log.length > 30) log.pop();
}

// ---------- discord client ----------
const client = new Client({
  intents: [
    GatewayIntentBits.Guilds,
    GatewayIntentBits.GuildMembers,     // privileged - must enable in dev portal
    GatewayIntentBits.GuildMessages,
    GatewayIntentBits.MessageContent,   // privileged - must enable in dev portal
    GatewayIntentBits.GuildVoiceStates, // needed to join/speak in voice channels
  ],
  partials: [Partials.Channel],
});

function getGuild() {
  if (process.env.GUILD_ID) {
    return client.guilds.cache.get(process.env.GUILD_ID) || null;
  }
  return client.guilds.cache.first() || null;
}

client.once('ready', () => {
  addLog(`Logged in as ${client.user.tag}`);
  registerSlashCommands();
});

// ---------- rule matching ----------
function ruleMatches(rule, message) {
  if (!rule.enabled) return false;
  if (rule.targetUserId && message.author.id !== rule.targetUserId) return false;

  const content = message.content.trim();
  if (rule.triggerType === 'any') return content.length > 0;
  if (rule.triggerType === 'contains') {
    return !!rule.triggerKeyword && content.toLowerCase().includes(rule.triggerKeyword.toLowerCase());
  }
  return /^\d+$/.test(content); // 'number' (default)
}

// ---------- TTS helpers ----------
async function synthesizeSpeech(text, { lang = 'en', slow = false } = {}) {
  const safeText = text && text.trim() ? text.trim() : randomDigitWord();
  const chunks = await googleTTS.getAllAudioUrls(safeText, { lang, slow, host: 'https://translate.google.com' });
  const buffers = [];
  for (const { url } of chunks) {
    const res = await fetch(url);
    if (!res.ok) throw new Error(`TTS request failed: ${res.status}`);
    buffers.push(Buffer.from(await res.arrayBuffer()));
  }
  return Buffer.concat(buffers);
}

async function sendChannelReply(rule, message, text) {
  const channelId = rule.channelId || message.channel.id;
  const channel = await client.channels.fetch(channelId);
  await channel.send(text);
  addLog(`Rule "${rule.name}" fired for ${message.author.username} -> sent "${text}" in #${channel.name || channelId}`);
}

async function sendTtsAttachment(rule, message) {
  const channelId = rule.channelId || message.channel.id;
  const channel = await client.channels.fetch(channelId);
  const buffer = await synthesizeSpeech(rule.replyText, { lang: rule.ttsLang, slow: rule.ttsSlow });
  await channel.send({ files: [{ attachment: buffer, name: 'reply.mp3' }] });
  addLog(`Rule "${rule.name}" fired for ${message.author.username} -> sent TTS audio in #${channel.name || channelId}`);
}

// ---------- voice playback (queued per-guild so overlapping triggers don't collide) ----------
const guildVoiceQueues = new Map();

function queueInGuild(guildId, task) {
  const previous = guildVoiceQueues.get(guildId) || Promise.resolve();
  const next = previous.catch(() => {}).then(task);
  guildVoiceQueues.set(guildId, next);
  return next;
}

const MAX_PLAYBACK_MS = 15_000; // hard cap so no clip/TTS line can hold a voice channel hostage
const guildActivePlayback = new Map(); // guildId -> { player, connection }, so it can be stopped on demand
const guildStayConnected = new Map(); // guildId -> { channelId, channelName }, set when told not to auto-leave

function stopGuildPlayback(guildId) {
  const active = guildActivePlayback.get(guildId);
  if (!active) return false;
  try { active.player.stop(true); } catch { /* already stopped */ }
  guildActivePlayback.delete(guildId);
  if (!guildStayConnected.has(guildId)) {
    try { active.connection.destroy(); } catch { /* already gone */ }
  }
  return true;
}

// Discord allows only one voice connection per guild, so "joining" a channel while already connected
// elsewhere in the same guild moves the existing connection rather than creating a second one.
async function joinAndStay(voiceChannel) {
  const guildId = voiceChannel.guild.id;
  const connection = joinVoiceChannel({
    channelId: voiceChannel.id,
    guildId,
    adapterCreator: voiceChannel.guild.voiceAdapterCreator,
    selfDeaf: true,
  });
  await entersState(connection, VoiceConnectionStatus.Ready, 10_000);
  guildStayConnected.set(guildId, { channelId: voiceChannel.id, channelName: voiceChannel.name });
  return connection;
}

function leaveVoiceChannel(guildId) {
  guildStayConnected.delete(guildId);
  const active = guildActivePlayback.get(guildId);
  if (active) {
    try { active.player.stop(true); } catch { /* already stopped */ }
    guildActivePlayback.delete(guildId);
  }
  const connection = getVoiceConnection(guildId);
  if (connection) {
    try { connection.destroy(); } catch { /* already gone */ }
    return true;
  }
  return false;
}

// Transcodes any input stream (mp3/wav/ogg/whatever) down to Discord's raw PCM format while applying
// live loudness normalization, so every clip is audible without being ear-splitting - regardless of
// whether the source file itself was ever pre-normalized.
function createNormalizedResource(sourceStream) {
  const transcoder = new prism.FFmpeg({
    args: [
      '-i', '-',
      '-analyzeduration', '0',
      '-loglevel', '0',
      '-af', LOUDNESS_FILTER,
      '-f', 's16le',
      '-ar', '48000',
      '-ac', '2',
    ],
  });
  const pcmStream = sourceStream.pipe(transcoder);
  pcmStream.on('error', () => { /* surfaced via the audio player's own 'error' event */ });
  return { resource: createAudioResource(pcmStream, { inputType: StreamType.Raw }), transcoder };
}

// resourceFactory returns a Readable/stream each call (so retries within @discordjs/voice re-read cleanly)
async function playAudioInVoiceChannel(voiceChannel, resourceFactory, { onDone, onError, stay = false } = {}) {
  const guildId = voiceChannel.guild.id;
  let connection;
  let stopTimer;
  let transcoder;
  try {
    connection = joinVoiceChannel({
      channelId: voiceChannel.id,
      guildId,
      adapterCreator: voiceChannel.guild.voiceAdapterCreator,
      selfDeaf: true,
    });
    await entersState(connection, VoiceConnectionStatus.Ready, 10_000);

    const player = createAudioPlayer();
    const built = createNormalizedResource(resourceFactory());
    const resource = built.resource;
    transcoder = built.transcoder;
    connection.subscribe(player);
    guildActivePlayback.set(guildId, { player, connection });

    player.on('error', (err) => { if (onError) onError(err); });
    player.play(resource);

    stopTimer = setTimeout(() => { try { player.stop(true); } catch { /* already stopped */ } }, MAX_PLAYBACK_MS);
    await entersState(player, AudioPlayerStatus.Idle, MAX_PLAYBACK_MS + 5_000);
    if (onDone) onDone();
  } catch (err) {
    if (onError) onError(err);
  } finally {
    if (stopTimer) clearTimeout(stopTimer);
    if (guildActivePlayback.get(guildId)?.connection === connection) guildActivePlayback.delete(guildId);
    if (transcoder) {
      try { transcoder.destroy(); } catch { /* already gone */ }
    }
    if (stay) guildStayConnected.set(guildId, { channelId: voiceChannel.id, channelName: voiceChannel.name });
    const shouldStay = stay || guildStayConnected.has(guildId);
    if (!shouldStay && connection) {
      try { connection.destroy(); } catch { /* already gone */ }
    }
  }
}

function queueVoiceReply(rule, message) {
  return queueInGuild(message.guild.id, async () => {
    const member = message.member || await message.guild.members.fetch(message.author.id).catch(() => null);
    const voiceChannel = member && member.voice && member.voice.channel;
    if (!voiceChannel) {
      addLog(`Rule "${rule.name}" wanted to speak but ${message.author.username} isn't in a voice channel`);
      return;
    }

    let buffer;
    try {
      buffer = await synthesizeSpeech(rule.replyText, { lang: rule.ttsLang, slow: rule.ttsSlow });
    } catch (err) {
      addLog(`ERROR in voice reply for rule "${rule.name}": ${err.message}`);
      return;
    }

    await playAudioInVoiceChannel(voiceChannel, () => Readable.from(buffer), {
      onDone: () => addLog(`Rule "${rule.name}" spoke in "${voiceChannel.name}" for ${message.author.username}`),
      onError: (err) => addLog(`ERROR in voice reply for rule "${rule.name}": ${err.message}`),
    });
  });
}

async function sendSoundboardAttachment(rule, message) {
  const safeName = rule.soundId ? path.basename(rule.soundId) : '';
  const filePath = safeName ? path.join(SOUNDS_DIR, safeName) : null;
  if (!filePath || !fs.existsSync(filePath)) {
    addLog(`Rule "${rule.name}" wanted to send a sound effect but none is selected`);
    return;
  }
  const channelId = rule.channelId || message.channel.id;
  const channel = await client.channels.fetch(channelId);
  await channel.send({ files: [{ attachment: filePath, name: safeName }] });
  addLog(`Rule "${rule.name}" fired for ${message.author.username} -> sent sound effect "${safeName}" in #${channel.name || channelId}`);
}

function queueSoundboardVoice(rule, message) {
  return queueInGuild(message.guild.id, async () => {
    const safeName = rule.soundId ? path.basename(rule.soundId) : '';
    const filePath = safeName ? path.join(SOUNDS_DIR, safeName) : null;
    if (!filePath || !fs.existsSync(filePath)) {
      addLog(`Rule "${rule.name}" wanted to play a sound effect but none is selected`);
      return;
    }
    if (!rule.voiceChannelId) {
      addLog(`Rule "${rule.name}" wanted to play a sound effect but no voice channel is selected`);
      return;
    }
    const voiceChannel = await message.guild.channels.fetch(rule.voiceChannelId).catch(() => null);
    if (!voiceChannel || !voiceChannel.isVoiceBased()) {
      addLog(`Rule "${rule.name}": selected voice channel could not be found`);
      return;
    }
    await playAudioInVoiceChannel(voiceChannel, () => fs.createReadStream(filePath), {
      onDone: () => addLog(`Rule "${rule.name}" played sound effect "${safeName}" in "${voiceChannel.name}"`),
      onError: (err) => addLog(`ERROR in rule "${rule.name}" sound effect: ${err.message}`),
    });
  });
}

// ---------- firing a rule ----------
async function fireRule(rule, message) {
  switch (rule.replyType) {
    case 'text':
      return sendChannelReply(rule, message, rule.replyText && rule.replyText.trim() ? rule.replyText.trim() : `${randomDigit()}`);
    case 'tts':
      return sendTtsAttachment(rule, message);
    case 'voice':
      return queueVoiceReply(rule, message);
    case 'soundboardAttachment':
      return sendSoundboardAttachment(rule, message);
    case 'soundboardVoice':
      return queueSoundboardVoice(rule, message);
    case 'digit':
    default:
      return sendChannelReply(rule, message, `${randomDigit()}`);
  }
}

client.on('messageCreate', async (message) => {
  if (!config.enabled) return;
  if (message.author.bot) return;

  for (const rule of config.rules) {
    if (!ruleMatches(rule, message)) continue;
    try {
      await fireRule(rule, message);
    } catch (err) {
      addLog(`ERROR firing rule "${rule.name}": ${err.message}`);
    }
  }
});

client.login(process.env.DISCORD_TOKEN).catch((err) => {
  console.error('Failed to log in. Check DISCORD_TOKEN in your .env file.');
  console.error(err.message);
  process.exit(1);
});

// ---------- soundboard ----------
function listSounds() {
  return fs.readdirSync(SOUNDS_DIR)
    .filter((f) => SOUND_EXTENSIONS.includes(path.extname(f).toLowerCase()))
    .map((f) => ({ id: f, name: path.basename(f, path.extname(f)) }))
    .sort((a, b) => a.name.localeCompare(b.name));
}

// Re-encodes in place as mp3 (loudnorm needs a real encode pass; the source container/codec doesn't matter after this).
async function normalizeSoundFile(filePath) {
  const dir = path.dirname(filePath);
  const base = path.basename(filePath, path.extname(filePath));
  const tmpOut = path.join(dir, `${base}.__norm__.mp3`);

  await execFileAsync(ffmpegPath, ['-y', '-i', filePath, '-af', LOUDNESS_FILTER, '-ar', '44100', '-b:a', '128k', tmpOut]);

  fs.unlinkSync(filePath);
  let finalPath = path.join(dir, `${base}.mp3`);
  let n = 1;
  while (fs.existsSync(finalPath)) {
    finalPath = path.join(dir, `${base} (${n++}).mp3`);
  }
  fs.renameSync(tmpOut, finalPath);
  return finalPath;
}

const soundUpload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, SOUNDS_DIR),
    filename: (req, file, cb) => {
      const ext = path.extname(file.originalname).toLowerCase();
      const rawName = (req.body && req.body.name) ? req.body.name : path.basename(file.originalname, ext);
      const base = rawName.replace(/[^a-z0-9 _-]/gi, '').trim() || 'sound';
      let name = `${base}${ext}`;
      let n = 1;
      while (fs.existsSync(path.join(SOUNDS_DIR, name))) {
        name = `${base} (${n++})${ext}`;
      }
      cb(null, name);
    },
  }),
  limits: { fileSize: 10 * 1024 * 1024 }, // 10 MB
  fileFilter: (req, file, cb) => {
    cb(null, SOUND_EXTENSIONS.includes(path.extname(file.originalname).toLowerCase()));
  },
});

async function resolveVoiceChannel(guild, { targetUserId, targetChannelId }) {
  if (targetChannelId) {
    const channel = await guild.channels.fetch(targetChannelId).catch(() => null);
    if (!channel || !channel.isVoiceBased()) throw new Error('That voice channel could not be found');
    return channel;
  }
  if (targetUserId) {
    const member = await guild.members.fetch(targetUserId).catch(() => null);
    const voiceChannel = member && member.voice && member.voice.channel;
    if (!voiceChannel) throw new Error('That user is not currently in a voice channel');
    return voiceChannel;
  }
  throw new Error('No target user or voice channel selected');
}

async function playSoundForTarget(soundId, { targetUserId, targetChannelId, stay }) {
  const guild = getGuild();
  if (!guild) throw new Error('Bot is not connected to a server');

  const safeName = path.basename(soundId);
  const filePath = path.join(SOUNDS_DIR, safeName);
  if (!fs.existsSync(filePath)) throw new Error('Sound not found');

  const voiceChannel = await resolveVoiceChannel(guild, { targetUserId, targetChannelId });

  // fire-and-forget: queue playback but don't make the caller wait for it to finish
  queueInGuild(guild.id, () => playAudioInVoiceChannel(
    voiceChannel,
    () => fs.createReadStream(filePath),
    {
      stay,
      onDone: () => addLog(`Soundboard: played "${safeName}" in "${voiceChannel.name}"`),
      onError: (err) => addLog(`ERROR playing soundboard clip "${safeName}": ${err.message}`),
    },
  ));
}

// ---------- slash commands ----------
const slashCommands = [
  new SlashCommandBuilder().setName('dashboard').setDescription('Get a one-time login link for the web dashboard'),
  new SlashCommandBuilder().setName('join').setDescription('Bot joins a voice channel and stays connected')
    .addChannelOption((opt) => opt.setName('channel').setDescription('Which voice channel (default: the one you\'re in)').addChannelTypes(ChannelType.GuildVoice)),
  new SlashCommandBuilder().setName('leave').setDescription('Bot leaves the voice channel'),
  new SlashCommandBuilder().setName('stop').setDescription('Stop whatever the bot is currently playing'),
  new SlashCommandBuilder().setName('play').setDescription('Play a soundboard clip in a voice channel')
    .addStringOption((opt) => opt.setName('clip').setDescription('Which clip to play').setRequired(true).setAutocomplete(true))
    .addChannelOption((opt) => opt.setName('channel').setDescription('Which voice channel (default: the one you\'re in)').addChannelTypes(ChannelType.GuildVoice))
    .addUserOption((opt) => opt.setName('user').setDescription('Play into whichever voice channel this user is currently in')),
  new SlashCommandBuilder().setName('say').setDescription('Speak a line out loud in a voice channel')
    .addStringOption((opt) => opt.setName('text').setDescription('What to say').setRequired(true))
    .addChannelOption((opt) => opt.setName('channel').setDescription('Which voice channel (default: the one you\'re in)').addChannelTypes(ChannelType.GuildVoice))
    .addUserOption((opt) => opt.setName('user').setDescription('Speak into whichever voice channel this user is currently in')),
].map((c) => c.toJSON());

async function registerSlashCommands() {
  try {
    const rest = new REST({ version: '10' }).setToken(process.env.DISCORD_TOKEN);
    if (process.env.GUILD_ID) {
      await rest.put(Routes.applicationGuildCommands(client.user.id, process.env.GUILD_ID), { body: slashCommands });
    } else {
      await rest.put(Routes.applicationCommands(client.user.id), { body: slashCommands });
    }
    addLog('Slash commands registered');
  } catch (err) {
    addLog(`ERROR registering slash commands: ${err.message}`);
  }
}

async function sayInChannel(guild, voiceChannel, text, speakerLabel) {
  const buffer = await synthesizeSpeech(text, { lang: 'en', slow: false });
  queueInGuild(guild.id, () => playAudioInVoiceChannel(voiceChannel, () => Readable.from(buffer), {
    onDone: () => addLog(`/say used by ${speakerLabel} in "${voiceChannel.name}"`),
    onError: (err) => addLog(`ERROR in /say: ${err.message}`),
  }));
}

// shared by /join, /play, /say: explicit channel option wins, then the given user's current
// channel, else the invoking member's own current channel
async function resolveCommandVoiceChannel(interaction) {
  const channelOpt = interaction.options.getChannel('channel');
  if (channelOpt) return channelOpt;

  const userOpt = interaction.options.getUser('user');
  if (userOpt) {
    const member = await interaction.guild.members.fetch(userOpt.id).catch(() => null);
    const voiceChannel = member && member.voice && member.voice.channel;
    if (!voiceChannel) throw new Error(`${userOpt.username} isn't in a voice channel.`);
    return voiceChannel;
  }

  const ownChannel = interaction.member.voice.channel;
  if (!ownChannel) throw new Error("You're not in a voice channel - join one, or pass a channel/user.");
  return ownChannel;
}

client.on('interactionCreate', async (interaction) => {
  if (interaction.isAutocomplete()) {
    if (interaction.commandName === 'play') {
      const focused = interaction.options.getFocused().toLowerCase();
      const matches = listSounds().filter((s) => s.name.toLowerCase().includes(focused)).slice(0, 25);
      await interaction.respond(matches.map((s) => ({ name: s.name.slice(0, 100), value: s.id })));
    }
    return;
  }

  if (!interaction.isChatInputCommand()) return;
  const { commandName, guild } = interaction;
  if (!guild) {
    await interaction.reply({ content: 'This only works in a server.', ephemeral: true });
    return;
  }

  try {
    if (commandName === 'dashboard') {
      const token = issueDashboardToken();
      const url = `${PUBLIC_URL}/login?token=${token}`;
      await interaction.reply({ content: `🔗 One-time dashboard link (expires in 10 minutes, single use):\n${url}`, ephemeral: true });
      return;
    }

    if (commandName === 'join') {
      let voiceChannel;
      try {
        voiceChannel = await resolveCommandVoiceChannel(interaction);
      } catch (err) {
        await interaction.reply({ content: err.message, ephemeral: true });
        return;
      }
      await joinAndStay(voiceChannel);
      addLog(`/join used by ${interaction.user.username} -> "${voiceChannel.name}"`);
      await interaction.reply({ content: `🔊 Joined "${voiceChannel.name}" and staying.`, ephemeral: true });
      return;
    }

    if (commandName === 'leave') {
      const left = leaveVoiceChannel(guild.id);
      await interaction.reply({ content: left ? '🚪 Left the voice channel.' : 'Not connected to a voice channel.', ephemeral: true });
      return;
    }

    if (commandName === 'stop') {
      const stopped = stopGuildPlayback(guild.id);
      await interaction.reply({ content: stopped ? '⏹ Stopped.' : 'Nothing is playing.', ephemeral: true });
      return;
    }

    if (commandName === 'play') {
      const soundId = interaction.options.getString('clip', true);
      await interaction.deferReply({ ephemeral: true });
      try {
        const voiceChannel = await resolveCommandVoiceChannel(interaction);
        await playSoundForTarget(soundId, { targetChannelId: voiceChannel.id, stay: false });
        await interaction.editReply(`▶️ Playing in "${voiceChannel.name}".`);
      } catch (err) {
        await interaction.editReply(`Couldn't play that: ${err.message}`);
      }
      return;
    }

    if (commandName === 'say') {
      const text = interaction.options.getString('text', true);
      await interaction.deferReply({ ephemeral: true });
      try {
        const voiceChannel = await resolveCommandVoiceChannel(interaction);
        await sayInChannel(guild, voiceChannel, text, interaction.user.username);
        await interaction.editReply(`🗣️ Speaking in "${voiceChannel.name}".`);
      } catch (err) {
        await interaction.editReply(`Couldn't do that: ${err.message}`);
      }
      return;
    }
  } catch (err) {
    addLog(`ERROR handling /${commandName}: ${err.message}`);
    if (interaction.deferred || interaction.replied) {
      interaction.editReply('Something went wrong.').catch(() => {});
    } else {
      interaction.reply({ content: 'Something went wrong.', ephemeral: true }).catch(() => {});
    }
  }
});

// ---------- dashboard web server ----------
const app = express();
app.set('trust proxy', 1); // WispByte/most hosts sit behind a proxy - needed for secure cookies to work correctly there
app.use((req, res, next) => {
  res.setHeader('X-Frame-Options', 'DENY'); // stop the dashboard being iframed for clickjacking
  res.setHeader('X-Content-Type-Options', 'nosniff');
  next();
});
app.use(express.json());
app.use(express.urlencoded({ extended: false }));
app.use(session({
  secret: SESSION_SECRET,
  resave: false,
  saveUninitialized: false,
  cookie: {
    maxAge: 7 * 24 * 60 * 60 * 1000,
    httpOnly: true,
    sameSite: 'lax', // blocks cross-site form/fetch submissions (CSRF) from other origins
    secure: process.env.DASHBOARD_HTTPS === 'true', // set DASHBOARD_HTTPS=true once the dashboard is served over https
  },
}));

// basic brute-force throttle on login attempts, keyed by IP
const loginAttempts = new Map(); // ip -> { count, resetAt }
function isRateLimited(ip) {
  const entry = loginAttempts.get(ip);
  const now = Date.now();
  if (!entry || now > entry.resetAt) {
    loginAttempts.set(ip, { count: 1, resetAt: now + 15 * 60 * 1000 });
    return false;
  }
  entry.count++;
  return entry.count > 20; // 20 attempts per 15 minutes per IP - the password is a random 8+ char string, so this is about blocking blind bots, not stopping a real brute force
}
function passwordMatches(input) {
  const a = Buffer.from(String(input));
  const b = Buffer.from(DASHBOARD_PASSWORD);
  if (a.length !== b.length) return false; // timingSafeEqual requires equal-length buffers
  return crypto.timingSafeEqual(a, b);
}

function loginPageHtml(error) {
  return `<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Trigger Bot — Login</title>
  <link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Geist:wght@500;600;700&display=swap" rel="stylesheet">
  <style>
    :root { --bg:#000000; --panel:#0a0a0a; --panel2:#111111; --fg:#ededed; --fg-dim:#a1a1a1; --border:#2a2a2a; --border-hover:#454545; --red:#e5484d; }
    * { box-sizing:border-box; }
    body { margin:0; min-height:100vh; display:flex; align-items:center; justify-content:center; font-family:"Geist",-apple-system,"Segoe UI",Roboto,sans-serif; background: var(--bg); color:var(--fg); }
    .box { background:var(--panel); border:1px solid var(--border); border-radius:6px; padding:28px; width:300px; }
    h1 { font-size:15px; font-weight:600; margin:0 0 4px; display:flex; align-items:center; gap:8px; }
    p.sub { color:var(--fg-dim); font-size:12.5px; margin:0 0 20px; }
    label { display:block; font-size:12px; color:var(--fg-dim); font-weight:500; margin-bottom:6px; }
    input { width:100%; padding:9px 12px; border-radius:6px; border:1px solid var(--border); background:var(--panel2); color:var(--fg); font-size:13px; margin-bottom:14px; }
    input:focus { outline:none; border-color:var(--fg-dim); }
    button { width:100%; padding:9px; border-radius:6px; border:1px solid var(--fg); background:var(--fg); color:#000; font-weight:600; font-size:13px; cursor:pointer; }
    button:hover { background:#d0d0d0; }
    .error { background:#e5484d14; color:var(--red); border:1px solid #e5484d40; border-radius:6px; padding:9px 12px; font-size:12px; margin-bottom:14px; }
  </style></head>
  <body>
    <div class="box">
      <h1>◆ Trigger Bot</h1>
      <p class="sub">Sign in to manage rules, the soundboard, and voice.</p>
      ${error ? '<div class="error">Wrong password. Try again.</div>' : ''}
      <form method="POST" action="/login">
        <label>Password</label>
        <input type="password" name="password" autofocus />
        <button type="submit">Log in</button>
      </form>
    </div>
  </body></html>`;
}

app.get('/login', (req, res) => {
  const token = req.query.token;
  if (typeof token === 'string' && consumeDashboardToken(token)) {
    req.session.authed = true;
    return res.redirect('/');
  }
  res.send(loginPageHtml(req.query.error === '1'));
});

app.post('/login', (req, res) => {
  if (isRateLimited(req.ip)) {
    return res.status(429).send(loginPageHtml(false)).end();
  }
  if (typeof req.body.password === 'string' && passwordMatches(req.body.password)) {
    req.session.authed = true;
    return res.redirect('/');
  }
  res.redirect('/login?error=1');
});

app.post('/logout', (req, res) => {
  req.session.destroy(() => res.redirect('/login'));
});

app.use((req, res, next) => {
  if (req.session && req.session.authed) return next();
  if (req.path.startsWith('/api/')) return res.status(401).json({ error: 'Not logged in' });
  return res.redirect('/login');
});

app.use(express.static(path.join(__dirname, 'public')));
app.use('/media/sounds', express.static(SOUNDS_DIR)); // lets the dashboard preview clips locally in the browser

let memberListCache = { guildId: null, at: 0, list: [] };
const MEMBER_CACHE_MS = 30_000; // avoid re-fetching the full member list (and hitting Discord's rate limit) on every dashboard poll

app.get('/api/status', async (req, res) => {
  const guild = getGuild();
  if (!guild) {
    return res.json({ ready: false, members: [], channels: [], config, log });
  }

  try {
    let memberList;
    if (memberListCache.guildId === guild.id && Date.now() - memberListCache.at < MEMBER_CACHE_MS) {
      memberList = memberListCache.list;
    } else {
      const members = await guild.members.fetch();
      memberList = members
        .filter((m) => !m.user.bot)
        .map((m) => ({ id: m.id, tag: m.user.tag, nickname: m.nickname }))
        .sort((a, b) => a.tag.localeCompare(b.tag));
      memberListCache = { guildId: guild.id, at: Date.now(), list: memberList };
    }

    const channelList = guild.channels.cache
      .filter((c) => c.isTextBased() && c.viewable)
      .map((c) => ({ id: c.id, name: c.name }))
      .sort((a, b) => a.name.localeCompare(b.name));

    const voiceChannelList = guild.channels.cache
      .filter((c) => c.isVoiceBased() && c.viewable)
      .map((c) => ({ id: c.id, name: c.name }))
      .sort((a, b) => a.name.localeCompare(b.name));

    res.json({
      ready: true,
      guildName: guild.name,
      members: memberList,
      channels: channelList,
      voiceChannels: voiceChannelList,
      ttsLangs: TTS_LANGS,
      sounds: listSounds(),
      isPlaying: guildActivePlayback.has(guild.id),
      connectedChannel: getVoiceConnection(guild.id) ? (guildStayConnected.get(guild.id) || null) : null,
      config,
      log,
    });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post('/api/config', (req, res) => {
  const { enabled, rules } = req.body;
  config = {
    enabled: !!enabled,
    rules: Array.isArray(rules) ? rules.map(normalizeRule) : [],
  };
  saveConfig(config);
  addLog(`Config updated (enabled=${config.enabled}, rules=${config.rules.length})`);
  res.json({ ok: true, config });
});

app.post('/api/sounds', soundUpload.single('sound'), async (req, res) => {
  if (!req.file) return res.status(400).json({ error: 'No valid audio file uploaded (mp3/wav/ogg/m4a, max 10MB)' });
  try {
    const finalPath = await normalizeSoundFile(req.file.path);
    addLog(`Soundboard: uploaded "${path.basename(finalPath)}" (volume normalized)`);
  } catch (err) {
    addLog(`Soundboard: uploaded "${req.file.filename}" but volume normalization failed: ${err.message}`);
  }
  res.json({ ok: true, sounds: listSounds() });
});

app.post('/api/sounds/normalize-all', async (req, res) => {
  const files = fs.readdirSync(SOUNDS_DIR).filter((f) => SOUND_EXTENSIONS.includes(path.extname(f).toLowerCase()));
  let done = 0;
  const errors = [];
  for (const f of files) {
    try {
      await normalizeSoundFile(path.join(SOUNDS_DIR, f));
      done++;
    } catch (err) {
      errors.push(`${f}: ${err.message}`);
    }
  }
  addLog(`Soundboard: normalized volume on ${done}/${files.length} clip(s)`);
  res.json({ ok: true, done, total: files.length, errors, sounds: listSounds() });
});

app.delete('/api/sounds/:id', (req, res) => {
  const safeName = path.basename(req.params.id);
  const filePath = path.join(SOUNDS_DIR, safeName);
  if (fs.existsSync(filePath)) {
    fs.unlinkSync(filePath);
    addLog(`Soundboard: removed "${safeName}"`);
  }
  res.json({ ok: true, sounds: listSounds() });
});

app.post('/api/sounds/:id/rename', (req, res) => {
  const { name } = req.body;
  if (!name || !name.trim()) return res.status(400).json({ error: 'A name is required' });

  const safeName = path.basename(req.params.id);
  const oldPath = path.join(SOUNDS_DIR, safeName);
  if (!fs.existsSync(oldPath)) return res.status(404).json({ error: 'Sound not found' });

  const ext = path.extname(safeName);
  const base = name.replace(/[^a-z0-9 _-]/gi, '').trim() || 'sound';
  let newName = `${base}${ext}`;
  let n = 1;
  while (newName !== safeName && fs.existsSync(path.join(SOUNDS_DIR, newName))) {
    newName = `${base} (${n++})${ext}`;
  }

  if (newName !== safeName) {
    fs.renameSync(oldPath, path.join(SOUNDS_DIR, newName));
    addLog(`Soundboard: renamed "${safeName}" to "${newName}"`);
  }
  res.json({ ok: true, sounds: listSounds() });
});

app.post('/api/sounds/:id/play', async (req, res) => {
  const { targetUserId, targetChannelId, stay } = req.body;
  if (!targetUserId && !targetChannelId) return res.status(400).json({ error: 'No target user or voice channel selected' });
  try {
    await playSoundForTarget(req.params.id, { targetUserId, targetChannelId, stay: !!stay });
    res.json({ ok: true });
  } catch (err) {
    res.status(400).json({ error: err.message });
  }
});

app.post('/api/voice/join', async (req, res) => {
  const { targetUserId, targetChannelId } = req.body;
  const guild = getGuild();
  if (!guild) return res.status(400).json({ error: 'Bot is not connected to a server' });
  try {
    const voiceChannel = await resolveVoiceChannel(guild, { targetUserId, targetChannelId });
    await joinAndStay(voiceChannel);
    addLog(`Soundboard: joined "${voiceChannel.name}" and will stay connected`);
    res.json({ ok: true, channelName: voiceChannel.name });
  } catch (err) {
    res.status(400).json({ error: err.message });
  }
});

app.post('/api/voice/leave', (req, res) => {
  const guild = getGuild();
  if (!guild) return res.status(400).json({ error: 'Bot is not connected to a server' });
  const left = leaveVoiceChannel(guild.id);
  if (left) addLog('Soundboard: left the voice channel');
  res.json({ ok: true, left });
});

app.post('/api/voice/stop', (req, res) => {
  const guild = getGuild();
  if (!guild) return res.status(400).json({ error: 'Bot is not connected to a server' });
  const stopped = stopGuildPlayback(guild.id);
  if (stopped) addLog('Soundboard: playback stopped manually');
  res.json({ ok: true, stopped });
});

app.listen(PORT, '0.0.0.0', () => {
  console.log(`Dashboard running on port ${PORT} (${PUBLIC_URL})`);
});
