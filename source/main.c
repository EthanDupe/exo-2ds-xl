/*
 * EXO - Nintendo 2DS XL / 3DS Port (citro2d + libctru + NDSP)
 * Original HTML5 js13k game by ai Doge & Jack Oatley (Music by Francis Fonye)
 *
 * Dual-Screen Architecture for New Nintendo 2DS XL:
 *  - Top Screen (400x240): Star System Viewport, Orbits, Power Relay Network,
 *    Celestial Bodies, Satellites, Mining Stations, Defense Platforms,
 *    Enemy Swarms, Projectiles, and World-Space Reticle.
 *  - Bottom Touch Screen (320x240): Interactive Radar Minimap (tap/drag to jump
 *    camera or place orbital stations), Resource & Wave HUD, 7-Button Construction
 *    Dock, Selected Unit Inspector & Weapon Level Upgrade Panel, and Tutorial Overlay.
 */

#include <3ds.h>
#include <citro2d.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define TOP_W 400.0f
#define TOP_H 240.0f
#define BOT_W 320.0f
#define BOT_H 240.0f

#define PI_F 3.14159265f
#define TWO_PI_F 6.28318530f

#define MAKE_COLOR(r, g, b, a) \
    ((u32)(r) | ((u32)(g) << 8) | ((u32)(b) << 16) | ((u32)(a) << 24))

#define MAX_BODIES      256
#define MAX_ENEMIES     512
#define MAX_PARTICLES   1024
#define MAX_ROCKETS     128
#define MAX_LINKS       512

typedef enum {
    BODY_SUN      = 0,
    BODY_PLANET   = 1,
    BODY_SAT      = 2,
    BODY_MINER    = 3,
    BODY_PLATFORM = 4,
    BODY_MOON     = 5
} BodyType;

typedef enum {
    WPN_LASER     = 0,
    WPN_BEAM      = 1,
    WPN_ROCKET    = 2,
    WPN_EMP       = 3,
    WPN_LIGHTNING = 4
} WeaponType;

typedef struct {
    int active;
    int id;
    BodyType type;
    char name[32];
    float x, y;
    float size;
    u32 color;
    float hp;
    int online;
    float turret_angle;

    /* Orbit info */
    int has_orbit;
    int parent_idx;
    float orbit_radius;
    float orbit_speed;
    float orbit_angle;

    /* Weapon info (for BODY_PLATFORM) */
    int has_weapon;
    WeaponType wpn_type;
    int wpn_level;
    int cooldown;
    float emp_radius;
    float beam_dir;
    int beam_active;
    int lightning_pts[12];
    int lightning_count;
} Body;

typedef struct {
    int active;
    float x, y, z;
    float angle;
    float hp;
    int target_idx;
    int fire_cd;
    float slow_factor;
    int slow_timer;
} Enemy;

typedef struct {
    int active;
    float x, y;
    float angle;
    float dist_left;
    float speed;
    u32 color;
} Particle;

typedef struct {
    int active;
    float x, y;
    float angle;
    int life;
    u32 color;
} Rocket;

typedef struct {
    u8 *data;
    u32 size;
    u32 sample_rate;
    u16 channels;
    u16 bits_per_sample;
    ndspWaveBuf wave_buf;
    int loaded;
} WavSound;

/* Global Game State */
static Body g_bodies[MAX_BODIES];
static int g_body_count = 0;
static int g_base_idx = 0;
static float g_system_size = 2500.0f;

static Enemy g_enemies[MAX_ENEMIES];
static Particle g_particles[MAX_PARTICLES];
static Rocket g_rockets[MAX_ROCKETS];
static int g_links[MAX_LINKS][2];
static int g_link_count = 0;

/* Player Resources (mirrors `u` in index.html) */
static float g_minerals = 50.0f;
static float g_energy = 10.0f;
static const float g_mineral_rate = 0.025f;
static const float g_energy_rate = 0.05f;
static const float g_relay_range = 501.0f;

/* Wave Spawner (`ub` in index.html) */
static int g_wave_num = 0;
static int g_wave_spawn_count = 30;
static int g_wave_interval_sec = 60;
static int g_wave_timer_frames = 3600;

/* Camera & Cursor (`z` and `D` in index.html) */
static float g_cam_x = 0.0f, g_cam_y = 0.0f;
static float g_cam_tx = 0.0f, g_cam_ty = 0.0f;
static float g_zoom = 0.35f, g_target_zoom = 0.35f;
static float g_tilt = 1.25f;
static float g_cursor_wx = 0.0f, g_cursor_wy = 0.0f;

/* UI & Construction State (`G` and `Y` in index.html) */
static int g_state = 0; /* 0 = Title, 1 = Playing, 2 = Paused */
static int g_selected_idx = -1;
static int g_build_active = 0;
static BodyType g_build_type = BODY_SAT;
static WeaponType g_build_wpn = WPN_LASER;
static int g_build_cost = 0;
static int g_build_parent = -1;
static float g_build_radius = 100.0f;
static int g_build_valid = 0;

static char g_status_msg[64] = "Welcome to Exo - 2DS XL Edition";
static int g_status_timer = 240;

/* Starfield vertices */
typedef struct { float x, y; u32 color; } Star;
static Star g_stars[180];

/* Audio */
static int g_ndsp_ok = 0;
static int g_music_muted = 0;
static int g_sfx_muted = 0;
static WavSound g_snd_music;
static WavSound g_snd_select;
static WavSound g_snd_laser[3];

/* Text rendering */
static C2D_TextBuf g_text_buf;

/* Helper Math */
static float randf(void) {
    return (float)rand() / (float)RAND_MAX;
}

static float clampf(float v, float lo, float hi) {
    return v < lo ? lo : (v > hi ? hi : v);
}

static float dist_sq(float x1, float y1, float x2, float y2) {
    float dx = x1 - x2, dy = y1 - y2;
    return dx * dx + dy * dy;
}

static float dist_f(float x1, float y1, float x2, float y2) {
    return sqrtf(dist_sq(x1, y1, x2, y2));
}

static float angle_between(float x1, float y1, float x2, float y2) {
    return atan2f(y1 - y2, x1 - x2);
}

static float wrap_two_pi(float a) {
    return a - floorf(a / TWO_PI_F) * TWO_PI_F;
}

static u32 hsl_to_color(float h_deg, float s_pct, float l_pct) {
    float h = fmodf(h_deg, 360.0f) / 360.0f;
    if (h < 0) h += 1.0f;
    float s = clampf(s_pct / 100.0f, 0.0f, 1.0f);
    float l = clampf(l_pct / 100.0f, 0.0f, 1.0f);
    float r, g, b;
    if (s == 0.0f) {
        r = g = b = l;
    } else {
        float q = l < 0.5f ? l * (1.0f + s) : l + s - l * s;
        float p = 2.0f * l - q;
        float t[3] = { h + 1.0f / 3.0f, h, h - 1.0f / 3.0f };
        float c[3];
        for (int i = 0; i < 3; i++) {
            if (t[i] < 0.0f) t[i] += 1.0f;
            if (t[i] > 1.0f) t[i] -= 1.0f;
            if (t[i] < 1.0f / 6.0f) c[i] = p + (q - p) * 6.0f * t[i];
            else if (t[i] < 0.5f)   c[i] = q;
            else if (t[i] < 2.0f / 3.0f) c[i] = p + (q - p) * (2.0f / 3.0f - t[i]) * 6.0f;
            else c[i] = p;
        }
        r = c[0]; g = c[1]; b = c[2];
    }
    return MAKE_COLOR((u8)(r * 255), (u8)(g * 255), (u8)(b * 255), 255);
}

static void set_status(const char *msg) {
    snprintf(g_status_msg, sizeof(g_status_msg), "%s", msg);
    g_status_timer = 210;
}

/* Audio Loader & Player */
static int wav_load(WavSound *snd, const char *path, bool loop) {
    memset(snd, 0, sizeof(*snd));
    FILE *f = fopen(path, "rb");
    if (!f) return -1;

    char riff[4], wave[4];
    u32 file_size = 0;
    if (fread(riff, 1, 4, f) != 4 ||
        fread(&file_size, 4, 1, f) != 1 ||
        fread(wave, 1, 4, f) != 4) {
        fclose(f);
        return -1;
    }
    if (memcmp(riff, "RIFF", 4) != 0 || memcmp(wave, "WAVE", 4) != 0) {
        fclose(f);
        return -1;
    }

    int got_data = 0;
    while (!got_data && !feof(f)) {
        char chunk_id[4];
        u32 chunk_size = 0;
        if (fread(chunk_id, 1, 4, f) != 4) break;
        if (fread(&chunk_size, 4, 1, f) != 1) break;

        if (memcmp(chunk_id, "fmt ", 4) == 0) {
            u16 audio_fmt = 0;
            fread(&audio_fmt, 2, 1, f);
            fread(&snd->channels, 2, 1, f);
            fread(&snd->sample_rate, 4, 1, f);
            u32 byte_rate = 0;
            u16 block_align = 0;
            fread(&byte_rate, 4, 1, f);
            fread(&block_align, 2, 1, f);
            fread(&snd->bits_per_sample, 2, 1, f);
            if (chunk_size > 16) fseek(f, chunk_size - 16, SEEK_CUR);
        } else if (memcmp(chunk_id, "data", 4) == 0) {
            snd->data = (u8 *)linearAlloc(chunk_size);
            if (!snd->data) {
                fclose(f);
                return -1;
            }
            snd->size = chunk_size;
            fread(snd->data, 1, chunk_size, f);
            got_data = 1;
        } else {
            fseek(f, chunk_size, SEEK_CUR);
        }
    }
    fclose(f);
    if (!got_data || !snd->data) return -1;

    snd->wave_buf.data_vaddr = snd->data;
    snd->wave_buf.nsamples = snd->size / (snd->channels * (snd->bits_per_sample / 8));
    snd->wave_buf.looping = loop;
    snd->wave_buf.status = NDSP_WBUF_FREE;
    DSP_FlushDataCache(snd->data, snd->size);
    snd->loaded = 1;
    return 0;
}

static void audio_init(void) {
    if (ndspInit() != 0) {
        g_ndsp_ok = 0;
        return;
    }
    g_ndsp_ok = 1;
    ndspSetOutputMode(NDSP_OUTPUT_STEREO);

    wav_load(&g_snd_music, "romfs:/audio/music.wav", true);
    wav_load(&g_snd_select, "romfs:/audio/select.wav", false);
    wav_load(&g_snd_laser[0], "romfs:/audio/laser0.wav", false);
    wav_load(&g_snd_laser[1], "romfs:/audio/laser1.wav", false);
    wav_load(&g_snd_laser[2], "romfs:/audio/laser2.wav", false);

    if (g_snd_music.loaded) {
        ndspChnReset(0);
        ndspChnSetInterp(0, NDSP_INTERP_LINEAR);
        ndspChnSetRate(0, (float)g_snd_music.sample_rate);
        ndspChnSetFormat(0, NDSP_FORMAT_STEREO_PCM16);
        float mix[12] = {0};
        mix[0] = 0.55f; mix[1] = 0.55f;
        ndspChnSetMix(0, mix);
        ndspChnWaveBufAdd(0, &g_snd_music.wave_buf);
    }

    for (int ch = 1; ch <= 4; ch++) {
        ndspChnReset(ch);
        ndspChnSetInterp(ch, NDSP_INTERP_LINEAR);
        ndspChnSetRate(ch, 44100.0f);
        ndspChnSetFormat(ch, NDSP_FORMAT_STEREO_PCM16);
        float mix[12] = {0};
        mix[0] = 0.45f; mix[1] = 0.45f;
        ndspChnSetMix(ch, mix);
    }
}

static void audio_play_sfx(WavSound *snd, int ch) {
    if (!g_ndsp_ok || g_sfx_muted || !snd || !snd->loaded) return;
    ndspChnWaveBufClear(ch);
    snd->wave_buf.status = NDSP_WBUF_FREE;
    DSP_FlushDataCache(snd->data, snd->size);
    ndspChnSetRate(ch, (float)snd->sample_rate);
    ndspChnWaveBufAdd(ch, &snd->wave_buf);
}

static void audio_cleanup(void) {
    if (g_ndsp_ok) {
        for (int ch = 0; ch <= 4; ch++) ndspChnReset(ch);
        ndspExit();
    }
    if (g_snd_music.data) linearFree(g_snd_music.data);
    if (g_snd_select.data) linearFree(g_snd_select.data);
    for (int i = 0; i < 3; i++) {
        if (g_snd_laser[i].data) linearFree(g_snd_laser[i].data);
    }
}

/* Particle & Explosion System (`ja` and `Aa` in index.html) */
static void spawn_particle(float x, float y, float angle, float dist, u32 color, float speed) {
    for (int i = 0; i < MAX_PARTICLES; i++) {
        if (!g_particles[i].active) {
            g_particles[i].active = 1;
            g_particles[i].x = x;
            g_particles[i].y = y;
            g_particles[i].angle = angle;
            g_particles[i].dist_left = dist - 50.0f;
            g_particles[i].speed = speed > 0.0f ? speed : 50.0f;
            g_particles[i].color = color;
            return;
        }
    }
}

static void spawn_explosion(float x, float y) {
    u32 col = MAKE_COLOR(255, 255, 0, 255);
    for (int i = 0; i < 36; i++) {
        spawn_particle(x, y, randf() * TWO_PI_F, 200.0f, col, 5.0f + 5.0f * randf());
    }
}

static void spawn_rocket(float x, float y, float angle, float dist, u32 color) {
    for (int i = 0; i < MAX_ROCKETS; i++) {
        if (!g_rockets[i].active) {
            g_rockets[i].active = 1;
            g_rockets[i].x = x;
            g_rockets[i].y = y;
            g_rockets[i].angle = angle;
            g_rockets[i].life = (int)(dist - 20.0f);
            g_rockets[i].color = color;
            return;
        }
    }
}

/* Enemy System (`r` in index.html) */
static void spawn_enemy(float x, float y, float angle) {
    for (int i = 0; i < MAX_ENEMIES; i++) {
        if (!g_enemies[i].active) {
            g_enemies[i].active = 1;
            g_enemies[i].x = x;
            g_enemies[i].y = y;
            g_enemies[i].z = 20.0f * randf();
            g_enemies[i].angle = angle;
            g_enemies[i].hp = 10.0f;
            g_enemies[i].target_idx = -1;
            g_enemies[i].fire_cd = (int)(10.0f * randf());
            g_enemies[i].slow_factor = 1.0f;
            g_enemies[i].slow_timer = 0;
            return;
        }
    }
}

static int find_nearest_enemy(float x, float y, float max_dist) {
    int best = -1;
    float best_d = max_dist;
    for (int i = 0; i < MAX_ENEMIES; i++) {
        if (!g_enemies[i].active) continue;
        float d = dist_f(x, y, g_enemies[i].x, g_enemies[i].y);
        if (d < best_d) {
            best_d = d;
            best = i;
        }
    }
    return best;
}

/* Body & Building System (`B` in index.html) */
static int get_build_cost(BodyType type, WeaponType wpn) {
    if (type == BODY_SAT) return 30;
    if (type == BODY_MINER) return 50;
    if (type == BODY_PLATFORM) {
        switch (wpn) {
            case WPN_LASER:     return 100;
            case WPN_BEAM:      return 150;
            case WPN_ROCKET:    return 200;
            case WPN_EMP:       return 250;
            case WPN_LIGHTNING: return 300;
        }
    }
    return 0;
}

static const char *get_build_name(BodyType type, WeaponType wpn) {
    if (type == BODY_SAT) return "Satellite";
    if (type == BODY_MINER) return "Mining Station";
    if (type == BODY_PLATFORM) {
        switch (wpn) {
            case WPN_LASER:     return "Laser Platform";
            case WPN_BEAM:      return "Beam Platform";
            case WPN_ROCKET:    return "Rocket Platform";
            case WPN_EMP:       return "EMP Platform";
            case WPN_LIGHTNING: return "Lightning Platform";
        }
    }
    return "Station";
}

static int create_body(BodyType type, const char *name, u32 color, float size,
                       float x, float y, int parent_idx, float orbit_r,
                       float orbit_spd, float orbit_ang) {
    if (g_body_count >= MAX_BODIES) return -1;
    int idx = g_body_count++;
    Body *b = &g_bodies[idx];
    memset(b, 0, sizeof(*b));
    b->active = 1;
    b->id = idx;
    b->type = type;
    snprintf(b->name, sizeof(b->name), "%s", name);
    b->x = x;
    b->y = y;
    b->size = size;
    b->color = color;
    b->hp = 100.0f;
    b->online = 0;
    b->emp_radius = 400.0f;

    if (parent_idx >= 0) {
        b->has_orbit = 1;
        b->parent_idx = parent_idx;
        b->orbit_radius = orbit_r;
        b->orbit_speed = (orbit_spd / 2.0f) / (orbit_r / 100.0f);
        if (type == BODY_PLANET) {
            b->orbit_speed /= (orbit_r / 10000.0f);
        }
        b->orbit_angle = orbit_ang;
        b->x = g_bodies[parent_idx].x + cosf(orbit_ang) * orbit_r;
        b->y = g_bodies[parent_idx].y + sinf(orbit_ang) * orbit_r;
    }
    return idx;
}

static void set_platform_weapon(int idx, WeaponType wpn, int level) {
    if (idx < 0 || idx >= g_body_count) return;
    Body *b = &g_bodies[idx];
    b->has_weapon = 1;
    b->wpn_type = wpn;
    b->wpn_level = level;
    b->cooldown = 0;
    b->emp_radius = 400.0f;
    b->beam_active = 0;
    b->lightning_count = 0;
}

static int find_nearest_body(float wx, float wy, int only_planet_or_sun) {
    int best = -1;
    float best_d = 999999.0f;
    for (int i = 0; i < g_body_count; i++) {
        if (!g_bodies[i].active) continue;
        if (only_planet_or_sun && g_bodies[i].type != BODY_SUN && g_bodies[i].type != BODY_PLANET)
            continue;
        float d = dist_f(wx, wy, g_bodies[i].x, g_bodies[i].y);
        if (d < best_d) {
            best_d = d;
            best = i;
        }
    }
    return best;
}

/* Power Relay Graph (`Ub` and `Vb` in index.html) */
static void update_power_network(void) {
    for (int i = 0; i < g_body_count; i++) {
        g_bodies[i].online = 0;
    }
    g_link_count = 0;
    if (g_base_idx < 0 || !g_bodies[g_base_idx].active) return;

    int queue[MAX_BODIES];
    int visited[MAX_BODIES] = {0};
    int q_head = 0, q_tail = 0;

    g_bodies[g_base_idx].online = 1;
    visited[g_base_idx] = 1;
    queue[q_tail++] = g_base_idx;

    while (q_head < q_tail) {
        int cur = queue[q_head++];
        Body *a = &g_bodies[cur];
        /* Only Base or Satellites relay connections */
        if (cur != g_base_idx && a->type != BODY_SAT) continue;

        for (int i = 0; i < g_body_count; i++) {
            if (!g_bodies[i].active || i == cur || visited[i]) continue;
            Body *d = &g_bodies[i];
            if (d->type != BODY_SAT && d->type != BODY_MINER && d->type != BODY_PLATFORM)
                continue;
            if (dist_f(a->x, a->y, d->x, d->y) <= g_relay_range) {
                d->online = 1;
                visited[i] = 1;
                if (g_link_count < MAX_LINKS) {
                    g_links[g_link_count][0] = cur;
                    g_links[g_link_count][1] = i;
                    g_link_count++;
                }
                queue[q_tail++] = i;
            }
        }
    }
}

/* Generate Solar System (`Ja.Y` in index.html) */
static void init_solar_system(void) {
    g_body_count = 0;
    memset(g_bodies, 0, sizeof(g_bodies));
    memset(g_enemies, 0, sizeof(g_enemies));
    memset(g_particles, 0, sizeof(g_particles));
    memset(g_rockets, 0, sizeof(g_rockets));

    int sun = create_body(BODY_SUN, "The Sun", hsl_to_color(60, 100, 50), 100.0f, 0.0f, 0.0f, -1, 0, 0, 0);
    int num_planets = 2 + (rand() % 3);
    float d = 1000.0f;
    int first_planet = -1;

    for (int f = 0; f < num_planets; f++) {
        float p_size = 20.0f + (float)(rand() % 30);
        u32 p_col = hsl_to_color(randf() * 360.0f, 39.0f, 62.0f);
        int p_idx = create_body(BODY_PLANET, "Planet", p_col, p_size, 0, 0, sun, d, 0.003f, randf() * TWO_PI_F);
        if (first_planet < 0) first_planet = p_idx;

        d += 100.0f * (float)((500 + (rand() % 500)) / 100);
        int num_moons = rand() % 3;
        float m_dist = 200.0f;
        for (int l = 0; l < num_moons; l++) {
            float m_size = floorf(0.1f * p_size + randf() * p_size * 0.3f);
            if (m_size < 4.0f) m_size = 4.0f;
            u32 m_col = hsl_to_color(randf() * 360.0f, 39.0f, 62.0f);
            create_body(BODY_MOON, "Moon", m_col, m_size, 0, 0, p_idx, m_dist, 0.01f, randf() * TWO_PI_F);
            m_dist += 100.0f;
        }
    }

    g_system_size = d;
    g_base_idx = first_planet;
    snprintf(g_bodies[g_base_idx].name, sizeof(g_bodies[g_base_idx].name), "Base Planet");
    g_bodies[g_base_idx].hp = 100.0f;

    /* Spawn 3 initial Mining Stations around Base Planet (`B.Z` in index.html) */
    create_body(BODY_MINER, "Mining Station", hsl_to_color(212, 100, 97), 5.0f, 0, 0, g_base_idx, 100.0f, 0.01f, 0.33f * TWO_PI_F);
    create_body(BODY_MINER, "Mining Station", hsl_to_color(212, 100, 97), 5.0f, 0, 0, g_base_idx, 100.0f, 0.01f, 0.66f * TWO_PI_F);
    create_body(BODY_MINER, "Mining Station", hsl_to_color(212, 100, 97), 5.0f, 0, 0, g_base_idx, 100.0f, 0.01f, 0.99f * TWO_PI_F);

    g_minerals = 50.0f;
    g_energy = 10.0f;
    g_wave_num = 0;
    g_wave_spawn_count = 30;
    g_wave_interval_sec = 60;
    g_wave_timer_frames = 60 * g_wave_interval_sec;

    g_cam_x = g_cam_tx = g_bodies[g_base_idx].x;
    g_cam_y = g_cam_ty = g_bodies[g_base_idx].y;
    g_zoom = g_target_zoom = 0.35f;
    g_cursor_wx = g_cam_x;
    g_cursor_wy = g_cam_y;
    g_selected_idx = g_base_idx;
    g_build_active = 0;

    update_power_network();
}

/* Weapon Update Logic (`ia`, `oa`, `sa`, `na`, `ra` in index.html) */
static void update_platform_weapon(Body *b) {
    if (!b->online || !b->has_weapon) return;
    float lvl_mult = 1.0f + 0.35f * (float)(b->wpn_level - 1);

    switch (b->wpn_type) {
        case WPN_LASER: {
            if (b->cooldown > 0) {
                b->cooldown--;
            } else {
                b->cooldown = 2;
                int e_idx = find_nearest_enemy(b->x, b->y, 1000.0f);
                if (e_idx >= 0 && g_energy >= 0.1f) {
                    g_energy -= 0.1f;
                    Enemy *e = &g_enemies[e_idx];
                    int miss = (randf() > 0.5f);
                    float d = miss ? 2000.0f : dist_f(b->x, b->y, e->x, e->y);
                    float ang = angle_between(b->x, b->y, e->x, e->y);
                    b->turret_angle = ang;
                    spawn_particle(b->x, b->y, ang, d, MAKE_COLOR(0, 255, 0, 255), 50.0f);
                    if (!miss) e->hp -= 2.0f * lvl_mult;
                    if (randf() > 0.7f) {
                        audio_play_sfx(&g_snd_laser[rand() % 3], 1 + (rand() % 3));
                    }
                }
            }
            break;
        }
        case WPN_BEAM: {
            b->beam_active = 0;
            if (g_energy >= 0.1f) {
                int e_idx = find_nearest_enemy(b->x, b->y, 1000.0f);
                if (e_idx >= 0) {
                    g_energy -= 0.1f;
                    b->beam_active = 1;
                    Enemy *target = &g_enemies[e_idx];
                    float f = angle_between(b->x, b->y, target->x, target->y);
                    float diff = wrap_two_pi(f - b->beam_dir + PI_F) - PI_F;
                    b->beam_dir += 0.02f * (diff >= 0.0f ? 1.0f : -1.0f);
                    b->turret_angle = b->beam_dir;
                    for (int i = 0; i < MAX_ENEMIES; i++) {
                        if (!g_enemies[i].active) continue;
                        float d = dist_f(b->x, b->y, g_enemies[i].x, g_enemies[i].y);
                        float k = wrap_two_pi(b->beam_dir - angle_between(b->x, b->y, g_enemies[i].x, g_enemies[i].y) + PI_F) - PI_F;
                        if (d < 1000.0f && fabsf(k) < 0.12f) {
                            g_enemies[i].hp -= 0.5f * lvl_mult;
                        }
                    }
                }
            }
            break;
        }
        case WPN_ROCKET: {
            if (b->cooldown > 0) {
                b->cooldown--;
            } else {
                b->cooldown = 20;
                int e_idx = find_nearest_enemy(b->x, b->y, 1500.0f);
                if (e_idx >= 0 && g_energy >= 0.1f) {
                    g_energy -= 0.1f;
                    Enemy *e = &g_enemies[e_idx];
                    float ang = angle_between(b->x, b->y, e->x, e->y);
                    b->turret_angle = ang;
                    spawn_rocket(b->x, b->y, ang, dist_f(b->x, b->y, e->x, e->y), MAKE_COLOR(80, 180, 255, 255));
                }
            }
            break;
        }
        case WPN_EMP: {
            if (b->cooldown > 0) b->cooldown--;
            if (b->cooldown <= 0 && g_energy >= 30.0f && find_nearest_enemy(b->x, b->y, 400.0f) >= 0) {
                b->emp_radius = 0.0f;
                b->cooldown = 120;
                g_energy -= 30.0f;
                for (int i = 0; i < MAX_ENEMIES; i++) {
                    if (!g_enemies[i].active) continue;
                    if (dist_f(b->x, b->y, g_enemies[i].x, g_enemies[i].y) < 400.0f) {
                        g_enemies[i].slow_factor = 0.05f;
                        g_enemies[i].slow_timer = 100 + 30 * (b->wpn_level - 1);
                    }
                }
            }
            if (b->emp_radius < 400.0f) b->emp_radius += 20.0f;
            break;
        }
        case WPN_LIGHTNING: {
            b->lightning_count = 0;
            int first = find_nearest_enemy(b->x, b->y, 300.0f);
            if (first >= 0) {
                int cur_e = first;
                for (int i = 0; i < MAX_ENEMIES && g_energy >= 0.01f && b->lightning_count < 10; i++) {
                    if (!g_enemies[i].active) continue;
                    if (dist_f(g_enemies[cur_e].x, g_enemies[cur_e].y, g_enemies[i].x, g_enemies[i].y) <= 300.0f) {
                        g_energy -= 0.01f;
                        cur_e = i;
                        b->lightning_pts[b->lightning_count++] = i;
                        g_enemies[i].hp -= 0.15f * lvl_mult;
                    }
                }
            }
            break;
        }
    }
}

/* Main Simulation Step (`Dc` in index.html) */
static void update_simulation(void) {
    if (g_status_timer > 0) g_status_timer--;

    if (g_state != 1) return;

    /* Check if Base Planet destroyed */
    if (g_base_idx < 0 || !g_bodies[g_base_idx].active || g_bodies[g_base_idx].hp <= 0.0f) {
        set_status("Base destroyed! Rebooting expedition...");
        init_solar_system();
        return;
    }

    /* Update power network */
    update_power_network();

    /* Update all bodies */
    for (int i = 0; i < g_body_count; i++) {
        Body *b = &g_bodies[i];
        if (!b->active) continue;
        if (b->hp <= 0.0f && i != g_base_idx) {
            spawn_explosion(b->x, b->y);
            b->active = 0;
            if (g_selected_idx == i) g_selected_idx = -1;
            continue;
        }
        if (b->has_orbit && b->parent_idx >= 0 && g_bodies[b->parent_idx].active) {
            b->orbit_angle += b->orbit_speed;
            b->x = g_bodies[b->parent_idx].x + cosf(b->orbit_angle) * b->orbit_radius;
            b->y = g_bodies[b->parent_idx].y + sinf(b->orbit_angle) * b->orbit_radius;
        }
        if (b->online) {
            if (b->type == BODY_SAT) {
                float factor = clampf(1.0f - b->orbit_radius / 500.0f, 0.1f, 1.0f);
                g_energy += g_energy_rate * factor;
            } else if (b->type == BODY_MINER) {
                float factor = clampf(1.0f - b->orbit_radius / 500.0f, 0.1f, 1.0f);
                g_minerals += g_mineral_rate * factor;
            } else if (b->type == BODY_PLATFORM) {
                update_platform_weapon(b);
            }
        }
    }

    /* Update Wave Spawner (`ub.update`) */
    if (--g_wave_timer_frames <= 0) {
        for (int i = 0; i < g_wave_spawn_count; i++) {
            float k = randf() * TWO_PI_F;
            spawn_enemy(cosf(k) * g_system_size, sinf(k) * g_system_size, k);
        }
        g_wave_num++;
        g_wave_interval_sec = (g_wave_interval_sec - 2 > 2) ? (g_wave_interval_sec - 2) : 2;
        g_wave_spawn_count += 30;
        g_wave_timer_frames = 60 * g_wave_interval_sec;
        set_status("Alert: Hostile wave inbound!");
    }

    /* Update Enemies (`r.update`) */
    for (int i = 0; i < MAX_ENEMIES; i++) {
        Enemy *e = &g_enemies[i];
        if (!e->active) continue;

        float speed = 5.0f;
        if (e->slow_timer > 0) {
            speed *= e->slow_factor;
            e->slow_timer--;
        }

        /* Find nearest online station or base planet */
        float best_d = 999999.0f;
        int best_t = g_base_idx;
        for (int j = 0; j < g_body_count; j++) {
            Body *b = &g_bodies[j];
            if (!b->active) continue;
            if ((b->type > BODY_PLANET || j == g_base_idx) && b->online) {
                float d = dist_f(e->x, e->y, b->x, b->y);
                if (d < best_d) {
                    best_d = d;
                    best_t = j;
                }
            }
        }
        e->target_idx = best_t;
        if (best_t >= 0 && g_bodies[best_t].active) {
            Body *t = &g_bodies[best_t];
            float target_ang = angle_between(e->x, e->y, t->x, t->y);
            e->angle += 0.02f * (wrap_two_pi(target_ang - e->angle + PI_F) - PI_F);
            e->x -= speed * cosf(e->angle);
            e->y -= speed * sinf(e->angle);

            if (--e->fire_cd <= 0) {
                e->fire_cd = 10;
                float d = dist_f(e->x, e->y, t->x, t->y);
                if (d < 500.0f) {
                    int miss = (randf() > 0.5f);
                    spawn_particle(e->x, e->y, target_ang, miss ? 2000.0f : d, MAKE_COLOR(255, 50, 50, 255), 50.0f);
                    if (!miss) t->hp -= 0.2f;
                }
            }
        }

        if (e->hp <= 0.0f) {
            spawn_explosion(e->x, e->y);
            e->active = 0;
            continue;
        }

        /* Simple flock separation */
        for (int j = i + 1; j < MAX_ENEMIES; j++) {
            if (!g_enemies[j].active) continue;
            if (dist_sq(e->x, e->y, g_enemies[j].x, g_enemies[j].y) < 200.0f) {
                float mx = (e->x - g_enemies[j].x) * 0.25f;
                float my = (e->y - g_enemies[j].y) * 0.25f;
                e->x += mx; e->y += my;
                g_enemies[j].x -= mx; g_enemies[j].y -= my;
                break;
            }
        }
    }

    /* Update Particles (`ja.update`) */
    for (int i = 0; i < MAX_PARTICLES; i++) {
        Particle *p = &g_particles[i];
        if (!p->active) continue;
        p->dist_left -= p->speed;
        if (p->dist_left <= 0.0f) {
            p->active = 0;
        } else {
            p->x -= cosf(p->angle) * p->speed;
            p->y -= sinf(p->angle) * p->speed;
        }
    }

    /* Update Rockets (`ta.update`) */
    for (int i = 0; i < MAX_ROCKETS; i++) {
        Rocket *r = &g_rockets[i];
        if (!r->active) continue;
        int e_idx = find_nearest_enemy(r->x, r->y, 500.0f);
        float d = (e_idx >= 0) ? dist_f(r->x, r->y, g_enemies[e_idx].x, g_enemies[e_idx].y) : 999.0f;
        if (--r->life <= 0 || d < 30.0f) {
            r->active = 0;
            spawn_explosion(r->x, r->y);
            if (e_idx >= 0 && d < 40.0f) {
                g_enemies[e_idx].hp -= 10.0f;
            }
        } else {
            if (e_idx >= 0) {
                float ang = angle_between(r->x, r->y, g_enemies[e_idx].x, g_enemies[e_idx].y);
                r->angle += 0.05f * (wrap_two_pi(ang - r->angle + PI_F) - PI_F);
            }
            r->x -= 20.0f * cosf(r->angle);
            r->y -= 20.0f * sinf(r->angle);
        }
    }
}

/* Drawing Helpers */
static void draw_text(const char *str, float x, float y, float scale, u32 color, int align_center) {
    C2D_Text text;
    C2D_TextParse(&text, g_text_buf, str);
    C2D_TextOptimize(&text);
    float w = 0, h = 0;
    C2D_TextGetDimensions(&text, scale, scale, &w, &h);
    float dx = align_center ? (x - w * 0.5f) : x;
    C2D_DrawText(&text, C2D_WithColor, dx, y, 0.0f, scale, scale, color);
}

static void world_to_top_screen(float wx, float wy, float *sx, float *sy) {
    *sx = TOP_W * 0.5f + (wx - g_cam_x) * g_zoom;
    *sy = TOP_H * 0.5f + ((wy - g_cam_y) / g_tilt) * g_zoom;
}

static void draw_circle_outline(float cx, float cy, float rx, float ry, int segs, u32 color, float thick) {
    float step = TWO_PI_F / (float)segs;
    float px = cx + rx;
    float py = cy;
    for (int i = 1; i <= segs; i++) {
        float a = i * step;
        float nx = cx + cosf(a) * rx;
        float ny = cy + sinf(a) * ry;
        C2D_DrawLine(px, py, color, nx, ny, color, thick, 0.0f);
        px = nx; py = ny;
    }
}

/* Render Top Screen (400x240) */
static void render_top_screen(void) {
    /* Space background */
    C2D_DrawRectSolid(0, 0, 0.0f, TOP_W, TOP_H, MAKE_COLOR(8, 14, 24, 255));

    /* Parallax Stars */
    for (int i = 0; i < 180; i++) {
        float sx = fmodf(g_stars[i].x - g_cam_x * 0.04f, TOP_W);
        float sy = fmodf(g_stars[i].y - g_cam_y * 0.04f, TOP_H);
        if (sx < 0) sx += TOP_W;
        if (sy < 0) sy += TOP_H;
        C2D_DrawRectSolid(sx, sy, 0.0f, 1.5f, 1.5f, g_stars[i].color);
    }

    if (g_state == 0) {
        draw_text("E X O", TOP_W * 0.5f, 45.0f, 1.6f, MAKE_COLOR(255, 255, 255, 255), 1);
        draw_text("Nintendo 2DS XL / 3DS Edition", TOP_W * 0.5f, 102.0f, 0.65f, MAKE_COLOR(0, 255, 160, 255), 1);
        draw_text("Press A / START or Tap Bottom Screen to Launch", TOP_W * 0.5f, 145.0f, 0.52f, MAKE_COLOR(255, 240, 120, 255), 1);
        draw_text("Original js13k Game by ai Doge & Jack Oatley | Music by Francis Fonye", TOP_W * 0.5f, 210.0f, 0.40f, MAKE_COLOR(160, 190, 220, 255), 1);
        return;
    }

    /* Draw Orbits */
    for (int i = 0; i < g_body_count; i++) {
        Body *b = &g_bodies[i];
        if (!b->active || !b->has_orbit || b->parent_idx < 0) continue;
        /* Only draw planet/moon orbits or selected body orbit to keep 60fps clean */
        if (b->type == BODY_PLANET || b->type == BODY_MOON || i == g_selected_idx) {
            float px, py;
            world_to_top_screen(g_bodies[b->parent_idx].x, g_bodies[b->parent_idx].y, &px, &py);
            float rx = b->orbit_radius * g_zoom;
            float ry = (b->orbit_radius / g_tilt) * g_zoom;
            if (rx > 3.0f && rx < 900.0f) {
                u32 ocol = (b->type == BODY_PLANET) ? MAKE_COLOR(90, 140, 200, 65) : MAKE_COLOR(120, 180, 220, 50);
                draw_circle_outline(px, py, rx, ry, 28, ocol, 1.0f);
            }
        }
    }

    /* Draw Power Relay Green Network Lines */
    u32 relay_col = MAKE_COLOR(0, 255, 80, 110);
    for (int i = 0; i < g_link_count; i++) {
        Body *a = &g_bodies[g_links[i][0]];
        Body *d = &g_bodies[g_links[i][1]];
        float x1, y1, x2, y2;
        world_to_top_screen(a->x, a->y, &x1, &y1);
        world_to_top_screen(d->x, d->y, &x2, &y2);
        C2D_DrawLine(x1, y1, relay_col, x2, y2, relay_col, 1.5f, 0.0f);
    }

    /* Draw Celestial Bodies & Stations */
    for (int i = 0; i < g_body_count; i++) {
        Body *b = &g_bodies[i];
        if (!b->active) continue;
        float sx, sy;
        world_to_top_screen(b->x, b->y, &sx, &sy);
        if (sx < -60.0f || sx > TOP_W + 60.0f || sy < -60.0f || sy > TOP_H + 60.0f)
            continue;

        float r = b->size * g_zoom;
        if (r < 2.5f) r = 2.5f;

        if (b->type == BODY_SUN) {
            C2D_DrawCircleSolid(sx, sy, 0.0f, r * 1.25f, MAKE_COLOR(255, 200, 50, 90));
            C2D_DrawCircleSolid(sx, sy, 0.0f, r, MAKE_COLOR(255, 250, 200, 255));
        } else if (b->type == BODY_PLANET || b->type == BODY_MOON) {
            C2D_DrawCircleSolid(sx, sy, 0.0f, r, b->color);
            if (i == g_base_idx) {
                draw_circle_outline(sx, sy, r + 3.0f, r + 3.0f, 16, MAKE_COLOR(0, 255, 140, 200), 1.5f);
            }
        } else if (b->type == BODY_SAT) {
            C2D_DrawRectSolid(sx - 3.0f, sy - 3.0f, 0.0f, 6.0f, 6.0f, MAKE_COLOR(100, 180, 255, 255));
            C2D_DrawCircleSolid(sx, sy - 6.0f, 0.0f, 1.8f, b->online ? MAKE_COLOR(0, 255, 0, 255) : MAKE_COLOR(255, 0, 0, 255));
        } else if (b->type == BODY_MINER) {
            /* Mining laser tether to parent planet */
            if (b->online && b->parent_idx >= 0) {
                float px, py;
                world_to_top_screen(g_bodies[b->parent_idx].x, g_bodies[b->parent_idx].y, &px, &py);
                C2D_DrawLine(sx, sy, MAKE_COLOR(220, 70, 70, 180), px, py, MAKE_COLOR(220, 70, 70, 180), 1.2f, 0.0f);
            }
            C2D_DrawRectSolid(sx - 3.0f, sy - 3.0f, 0.0f, 6.0f, 6.0f, MAKE_COLOR(220, 90, 90, 255));
            C2D_DrawCircleSolid(sx, sy - 6.0f, 0.0f, 1.8f, b->online ? MAKE_COLOR(0, 255, 0, 255) : MAKE_COLOR(255, 0, 0, 255));
        } else if (b->type == BODY_PLATFORM) {
            C2D_DrawCircleSolid(sx, sy, 0.0f, 4.0f, MAKE_COLOR(200, 80, 60, 255));
            C2D_DrawCircleSolid(sx, sy - 7.0f, 0.0f, 1.8f, b->online ? MAKE_COLOR(0, 255, 0, 255) : MAKE_COLOR(255, 0, 0, 255));

            /* Active Weapon Visuals */
            if (b->online && b->has_weapon) {
                if (b->wpn_type == WPN_BEAM && b->beam_active) {
                    float bx, by;
                    world_to_top_screen(b->x - 1000.0f * cosf(b->beam_dir), b->y - 1000.0f * sinf(b->beam_dir), &bx, &by);
                    C2D_DrawLine(sx, sy, MAKE_COLOR(255, 255, 0, 220), bx, by, MAKE_COLOR(255, 180, 0, 40), 3.0f, 0.0f);
                } else if (b->wpn_type == WPN_EMP && b->emp_radius < 400.0f) {
                    draw_circle_outline(sx, sy, b->emp_radius * g_zoom, (b->emp_radius / g_tilt) * g_zoom, 20, MAKE_COLOR(198, 226, 255, 200), 1.5f);
                } else if (b->wpn_type == WPN_LIGHTNING && b->lightning_count > 0) {
                    float lx = sx, ly = sy;
                    for (int k = 0; k < b->lightning_count; k++) {
                        int ei = b->lightning_pts[k];
                        if (g_enemies[ei].active) {
                            float ex, ey;
                            world_to_top_screen(g_enemies[ei].x, g_enemies[ei].y, &ex, &ey);
                            C2D_DrawLine(lx, ly, MAKE_COLOR(0, 255, 255, 255), ex, ey, MAKE_COLOR(0, 255, 255, 255), 1.5f, 0.0f);
                            lx = ex; ly = ey;
                        }
                    }
                }
            }
        }
    }

    /* Draw Enemies */
    u32 enemy_col = MAKE_COLOR(255, 45, 45, 255);
    for (int i = 0; i < MAX_ENEMIES; i++) {
        if (!g_enemies[i].active) continue;
        float sx, sy;
        world_to_top_screen(g_enemies[i].x, g_enemies[i].y, &sx, &sy);
        if (sx < -10.0f || sx > TOP_W + 10.0f || sy < -10.0f || sy > TOP_H + 10.0f) continue;
        C2D_DrawCircleSolid(sx, sy, 0.0f, 2.2f, enemy_col);
    }

    /* Draw Particles & Lasers */
    for (int i = 0; i < MAX_PARTICLES; i++) {
        if (!g_particles[i].active) continue;
        float sx, sy, ex, ey;
        world_to_top_screen(g_particles[i].x, g_particles[i].y, &sx, &sy);
        world_to_top_screen(g_particles[i].x + 12.0f * cosf(g_particles[i].angle),
                            g_particles[i].y + 12.0f * sinf(g_particles[i].angle), &ex, &ey);
        C2D_DrawLine(sx, sy, g_particles[i].color, ex, ey, g_particles[i].color, 1.5f, 0.0f);
    }

    /* Draw Rockets */
    for (int i = 0; i < MAX_ROCKETS; i++) {
        if (!g_rockets[i].active) continue;
        float sx, sy;
        world_to_top_screen(g_rockets[i].x, g_rockets[i].y, &sx, &sy);
        C2D_DrawCircleSolid(sx, sy, 0.0f, 2.5f, MAKE_COLOR(0, 255, 120, 255));
    }

    /* Draw Placement Ring if building (`G.g` in index.html) */
    if (g_build_active && g_build_parent >= 0 && g_bodies[g_build_parent].active) {
        float px, py;
        world_to_top_screen(g_bodies[g_build_parent].x, g_bodies[g_build_parent].y, &px, &py);
        float rx = g_build_radius * g_zoom;
        float ry = (g_build_radius / g_tilt) * g_zoom;
        u32 bcol = g_build_valid ? MAKE_COLOR(0, 255, 0, 190) : MAKE_COLOR(255, 0, 0, 190);
        draw_circle_outline(px, py, rx, ry, 28, bcol, 2.0f);
    }

    /* Draw Reticle at Cursor */
    float cx, cy;
    world_to_top_screen(g_cursor_wx, g_cursor_wy, &cx, &cy);
    C2D_DrawLine(cx - 6, cy, MAKE_COLOR(255, 255, 255, 200), cx + 6, cy, MAKE_COLOR(255, 255, 255, 200), 1.0f, 0.0f);
    C2D_DrawLine(cx, cy - 6, MAKE_COLOR(255, 255, 255, 200), cx, cy + 6, MAKE_COLOR(255, 255, 255, 200), 1.0f, 0.0f);

    /* Top HUD Bar */
    C2D_DrawRectSolid(0, 0, 0.0f, TOP_W, 24.0f, MAKE_COLOR(0, 0, 0, 170));
    char hud_buf[128];
    snprintf(hud_buf, sizeof(hud_buf), "BASE: %d%%   WAVES: %d   NEXT: %ds   MIN: %d   NRG: %d",
             (int)g_bodies[g_base_idx].hp, g_wave_num, g_wave_timer_frames / 60,
             (int)g_minerals, (int)g_energy);
    draw_text(hud_buf, TOP_W * 0.5f, 4.0f, 0.44f, MAKE_COLOR(255, 255, 255, 255), 1);

    if (g_state == 2) {
        C2D_DrawRectSolid(130, 100, 0.0f, 140, 36, MAKE_COLOR(0, 0, 0, 210));
        draw_text("PAUSED (Press Y)", TOP_W * 0.5f, 110.0f, 0.55f, MAKE_COLOR(255, 255, 0, 255), 1);
    }

    if (g_status_timer > 0) {
        C2D_DrawRectSolid(0, TOP_H - 20.0f, 0.0f, TOP_W, 20.0f, MAKE_COLOR(0, 0, 0, 160));
        draw_text(g_status_msg, TOP_W * 0.5f, TOP_H - 17.0f, 0.42f, MAKE_COLOR(140, 240, 255, 255), 1);
    }
}

/* Render Bottom Touch Screen (320x240) */
static void render_bottom_screen(void) {
    C2D_DrawRectSolid(0, 0, 0.0f, BOT_W, BOT_H, MAKE_COLOR(14, 20, 34, 255));

    /* 1. Interactive Radar Minimap (Left: x=8..168, y=8..168, 160x160) */
    float map_x = 8.0f, map_y = 8.0f, map_sz = 160.0f;
    float map_cx = map_x + map_sz * 0.5f;
    float map_cy = map_y + map_sz * 0.5f;
    float map_scale = (map_sz * 0.46f) / g_system_size;

    C2D_DrawRectSolid(map_x, map_y, 0.0f, map_sz, map_sz, MAKE_COLOR(6, 10, 18, 255));
    for (int i = 0; i < g_body_count; i++) {
        Body *b = &g_bodies[i];
        if (!b->active) continue;
        float mx = map_cx + b->x * map_scale;
        float my = map_cy + b->y * map_scale;
        if (mx < map_x || mx > map_x + map_sz || my < map_y || my > map_y + map_sz) continue;
        float mr = (b->type == BODY_SUN) ? 4.0f : (b->type == BODY_PLANET ? 2.5f : 1.5f);
        u32 mcol = (i == g_base_idx) ? MAKE_COLOR(0, 255, 140, 255) : b->color;
        C2D_DrawCircleSolid(mx, my, 0.0f, mr, mcol);
    }
    for (int i = 0; i < MAX_ENEMIES; i++) {
        if (!g_enemies[i].active) continue;
        float mx = map_cx + g_enemies[i].x * map_scale;
        float my = map_cy + g_enemies[i].y * map_scale;
        if (mx >= map_x && mx <= map_x + map_sz && my >= map_y && my <= map_y + map_sz) {
            C2D_DrawRectSolid(mx, my, 0.0f, 1.5f, 1.5f, MAKE_COLOR(255, 50, 50, 255));
        }
    }
    /* Camera viewport indicator on radar */
    float vx = map_cx + g_cam_x * map_scale;
    float vy = map_cy + g_cam_y * map_scale;
    C2D_DrawRectSolid(vx - 3.0f, vy - 2.0f, 0.0f, 6.0f, 4.0f, MAKE_COLOR(255, 255, 255, 180));
    draw_text("TACTICAL RADAR (Tap/Drag)", map_x + 4.0f, map_y + 3.0f, 0.36f, MAKE_COLOR(130, 190, 255, 255), 0);

    /* 2. Right Inspector & Upgrade Panel (x=174..312, y=8..168) */
    C2D_DrawRectSolid(174.0f, 8.0f, 0.0f, 138.0f, 160.0f, MAKE_COLOR(22, 32, 52, 255));
    if (g_build_active) {
        draw_text("BUILD MODE", 243.0f, 14.0f, 0.45f, MAKE_COLOR(0, 255, 140, 255), 1);
        draw_text(get_build_name(g_build_type, g_build_wpn), 243.0f, 32.0f, 0.40f, MAKE_COLOR(255, 255, 255, 255), 1);
        char cbuf[48];
        snprintf(cbuf, sizeof(cbuf), "Cost: %d Min", g_build_cost);
        draw_text(cbuf, 243.0f, 48.0f, 0.40f, MAKE_COLOR(255, 220, 100, 255), 1);
        snprintf(cbuf, sizeof(cbuf), "Orbit: %d", (int)g_build_radius);
        draw_text(cbuf, 243.0f, 66.0f, 0.40f, MAKE_COLOR(180, 220, 255, 255), 1);
        draw_text("D-Pad Up/Dn: Orbit", 243.0f, 86.0f, 0.36f, MAKE_COLOR(200, 200, 200, 255), 1);
        draw_text("A: Confirm | B: Cancel", 243.0f, 102.0f, 0.36f, MAKE_COLOR(200, 200, 200, 255), 1);

        /* Confirm & Cancel touch buttons */
        C2D_DrawRectSolid(182.0f, 125.0f, 0.0f, 58.0f, 34.0f, g_build_valid ? MAKE_COLOR(0, 150, 70, 255) : MAKE_COLOR(70, 70, 70, 255));
        draw_text("PLACE", 211.0f, 136.0f, 0.42f, MAKE_COLOR(255, 255, 255, 255), 1);
        C2D_DrawRectSolid(246.0f, 125.0f, 0.0f, 58.0f, 34.0f, MAKE_COLOR(160, 45, 45, 255));
        draw_text("CANCEL", 275.0f, 136.0f, 0.42f, MAKE_COLOR(255, 255, 255, 255), 1);
    } else if (g_selected_idx >= 0 && g_bodies[g_selected_idx].active) {
        Body *b = &g_bodies[g_selected_idx];
        draw_text(b->name, 243.0f, 14.0f, 0.44f, MAKE_COLOR(255, 255, 255, 255), 1);
        char ibuf[64];
        snprintf(ibuf, sizeof(ibuf), "HP: %d%% | %s", (int)b->hp, b->online ? "ONLINE" : "OFFLINE");
        draw_text(ibuf, 243.0f, 34.0f, 0.38f, b->online ? MAKE_COLOR(0, 255, 120, 255) : MAKE_COLOR(255, 100, 100, 255), 1);

        if (b->type == BODY_PLATFORM && b->has_weapon) {
            const char *wnames[5] = {"Lasers", "Beam", "Rockets", "EMP", "Lightning"};
            snprintf(ibuf, sizeof(ibuf), "%s (Lv.%d)", wnames[b->wpn_type], b->wpn_level);
            draw_text(ibuf, 243.0f, 54.0f, 0.40f, MAKE_COLOR(255, 230, 110, 255), 1);

            int upg_cost = 75 * b->wpn_level;
            C2D_DrawRectSolid(184.0f, 78.0f, 0.0f, 118.0f, 34.0f,
                              (g_minerals >= upg_cost) ? MAKE_COLOR(30, 130, 200, 255) : MAKE_COLOR(55, 65, 80, 255));
            snprintf(ibuf, sizeof(ibuf), "UPGRADE (%dM)", upg_cost);
            draw_text(ibuf, 243.0f, 89.0f, 0.40f, MAKE_COLOR(255, 255, 255, 255), 1);
        } else {
            draw_text("X: Center Camera", 243.0f, 65.0f, 0.36f, MAKE_COLOR(170, 200, 230, 255), 1);
            draw_text("L/R: Zoom In/Out", 243.0f, 83.0f, 0.36f, MAKE_COLOR(170, 200, 230, 255), 1);
            draw_text("Y: Pause Game", 243.0f, 101.0f, 0.36f, MAKE_COLOR(170, 200, 230, 255), 1);
        }

        /* Audio Mute Toggle Button */
        C2D_DrawRectSolid(184.0f, 126.0f, 0.0f, 118.0f, 32.0f, MAKE_COLOR(45, 60, 85, 255));
        draw_text(g_music_muted ? "AUDIO: MUTED" : "AUDIO: ON", 243.0f, 136.0f, 0.40f, MAKE_COLOR(220, 240, 255, 255), 1);
    }

    /* 3. Bottom 7-Button Construction Dock (y=176..234) */
    const char *labels[7] = {"SAT", "MINE", "LASR", "BEAM", "RCKT", "EMP", "LGHT"};
    const int costs[7]    = {30,    50,     100,    150,    200,    250,   300};
    for (int i = 0; i < 7; i++) {
        float bx = 6.0f + i * 44.5f;
        float by = 176.0f;
        int can_afford = (g_minerals >= (float)costs[i]);
        u32 bg = can_afford ? MAKE_COLOR(32, 54, 86, 255) : MAKE_COLOR(22, 26, 36, 255);
        C2D_DrawRectSolid(bx, by, 0.0f, 41.0f, 56.0f, bg);
        draw_text(labels[i], bx + 20.5f, by + 10.0f, 0.38f,
                  can_afford ? MAKE_COLOR(255, 255, 255, 255) : MAKE_COLOR(110, 120, 135, 255), 1);
        char cstr[16];
        snprintf(cstr, sizeof(cstr), "%dM", costs[i]);
        draw_text(cstr, bx + 20.5f, by + 32.0f, 0.36f,
                  can_afford ? MAKE_COLOR(0, 255, 150, 255) : MAKE_COLOR(130, 90, 90, 255), 1);
    }
}

/* Input Handling for 2DS XL / 3DS */
static void handle_input(void) {
    hidScanInput();
    u32 kDown = hidKeysDown();
    u32 kHeld = hidKeysHeld();

    if (g_state == 0) {
        if (kDown & (KEY_A | KEY_START | KEY_TOUCH)) {
            g_state = 1;
            audio_play_sfx(&g_snd_select, 1);
        }
        return;
    }

    if (kDown & KEY_Y) {
        g_state = (g_state == 1) ? 2 : 1;
        audio_play_sfx(&g_snd_select, 1);
    }

    /* Circle Pad pans camera & world reticle */
    circlePosition cpad;
    hidCircleRead(&cpad);
    float pan_speed = 12.0f / g_zoom;
    if (abs(cpad.dx) > 25) {
        g_cam_tx += (cpad.dx / 155.0f) * pan_speed;
        g_cursor_wx = g_cam_tx;
    }
    if (abs(cpad.dy) > 25) {
        g_cam_ty -= (cpad.dy / 155.0f) * pan_speed;
        g_cursor_wy = g_cam_ty;
    }

    /* L / R Shoulder Buttons Zoom Out / In */
    if (kHeld & KEY_L) g_target_zoom = clampf(g_target_zoom - 0.015f, 0.10f, 1.50f);
    if (kHeld & KEY_R) g_target_zoom = clampf(g_target_zoom + 0.015f, 0.10f, 1.50f);

    /* X Centers on Base Planet */
    if (kDown & KEY_X) {
        g_cam_tx = g_bodies[g_base_idx].x;
        g_cam_ty = g_bodies[g_base_idx].y;
        g_cursor_wx = g_cam_tx;
        g_cursor_wy = g_cam_ty;
        g_selected_idx = g_base_idx;
        set_status("Camera centered on Base Planet");
    }

    /* Build Mode Orbit Adjustment & Placement */
    if (g_build_active) {
        if (kDown & KEY_DUP)   g_build_radius = clampf(g_build_radius + 100.0f, 100.0f, 800.0f);
        if (kDown & KEY_DDOWN) g_build_radius = clampf(g_build_radius - 100.0f, 100.0f, 800.0f);
        if (kDown & (KEY_DLEFT | KEY_DRIGHT)) {
            /* Cycle parent planet/sun */
            for (int step = 1; step <= g_body_count; step++) {
                int idx = (g_build_parent + step) % g_body_count;
                if (g_bodies[idx].active && (g_bodies[idx].type == BODY_SUN || g_bodies[idx].type == BODY_PLANET)) {
                    g_build_parent = idx;
                    g_cam_tx = g_bodies[idx].x;
                    g_cam_ty = g_bodies[idx].y;
                    break;
                }
            }
        }
        if (g_build_parent >= 0 && g_bodies[g_build_parent].active) {
            float max_r = 20.0f * g_bodies[g_build_parent].size;
            if (g_build_radius > max_r) g_build_radius = 100.0f * floorf(max_r / 100.0f);
            if (g_build_radius < 100.0f) g_build_radius = 100.0f;
            g_build_valid = (g_minerals >= (float)g_build_cost);
        } else {
            g_build_valid = 0;
        }

        if (kDown & KEY_B) {
            g_build_active = 0;
            set_status("Construction canceled");
        } else if ((kDown & KEY_A) && g_build_valid) {
            float ang = randf() * TWO_PI_F;
            int new_idx = -1;
            if (g_build_type == BODY_SAT) {
                new_idx = create_body(BODY_SAT, "Satellite", hsl_to_color(160, 100, 50), 3.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
            } else if (g_build_type == BODY_MINER) {
                new_idx = create_body(BODY_MINER, "Mining Station", hsl_to_color(212, 100, 97), 3.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
            } else if (g_build_type == BODY_PLATFORM) {
                new_idx = create_body(BODY_PLATFORM, get_build_name(g_build_type, g_build_wpn), hsl_to_color(33, 100, 50), 4.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
                set_platform_weapon(new_idx, g_build_wpn, 1);
            }
            if (new_idx >= 0) {
                g_minerals -= (float)g_build_cost;
                g_selected_idx = new_idx;
                set_status("Constructed orbital unit!");
                audio_play_sfx(&g_snd_select, 1);
            }
            g_build_active = 0;
        }
    } else {
        /* Select nearest body to cursor with A */
        if (kDown & KEY_A) {
            int near_idx = find_nearest_body(g_cursor_wx, g_cursor_wy, 0);
            if (near_idx >= 0) {
                g_selected_idx = near_idx;
                g_cam_tx = g_bodies[near_idx].x;
                g_cam_ty = g_bodies[near_idx].y;
                audio_play_sfx(&g_snd_select, 1);
            }
        }
    }

    /* Touch Screen Input */
    if (kHeld & KEY_TOUCH) {
        touchPosition touch;
        hidTouchRead(&touch);
        float tx = (float)touch.px;
        float ty = (float)touch.py;

        /* Radar Minimap Drag/Tap (x=8..168, y=8..168) */
        if (tx >= 8.0f && tx <= 168.0f && ty >= 8.0f && ty <= 168.0f) {
            float map_cx = 88.0f, map_cy = 88.0f;
            float map_scale = (160.0f * 0.46f) / g_system_size;
            float wx = (tx - map_cx) / map_scale;
            float wy = (ty - map_cy) / map_scale;
            g_cam_tx = wx;
            g_cam_ty = wy;
            g_cursor_wx = wx;
            g_cursor_wy = wy;
            if (kDown & KEY_TOUCH) {
                int near_b = find_nearest_body(wx, wy, g_build_active ? 1 : 0);
                if (near_b >= 0) {
                    if (g_build_active) g_build_parent = near_b;
                    else g_selected_idx = near_b;
                }
            }
        }
    }

    if (kDown & KEY_TOUCH) {
        touchPosition touch;
        hidTouchRead(&touch);
        float tx = (float)touch.px;
        float ty = (float)touch.py;

        /* Bottom 7-Button Construction Dock (y=176..234) */
        if (ty >= 176.0f && ty <= 234.0f) {
            int slot = (int)((tx - 6.0f) / 44.5f);
            if (slot >= 0 && slot < 7) {
                BodyType btype = (slot == 0) ? BODY_SAT : (slot == 1 ? BODY_MINER : BODY_PLATFORM);
                WeaponType wtype = (slot >= 2) ? (WeaponType)(slot - 2) : WPN_LASER;
                int cost = get_build_cost(btype, wtype);
                if (g_minerals >= (float)cost) {
                    g_build_active = 1;
                    g_build_type = btype;
                    g_build_wpn = wtype;
                    g_build_cost = cost;
                    int p = find_nearest_body(g_cam_x, g_cam_y, 1);
                    g_build_parent = (p >= 0) ? p : g_base_idx;
                    g_build_radius = 100.0f;
                    g_build_valid = 1;
                    set_status("Select parent planet & orbit radius");
                    audio_play_sfx(&g_snd_select, 1);
                } else {
                    set_status("Insufficient minerals!");
                }
            }
        }

        /* Right Panel Buttons */
        if (g_build_active) {
            if (tx >= 182.0f && tx <= 240.0f && ty >= 125.0f && ty <= 159.0f && g_build_valid) {
                /* Trigger PLACE */
                float ang = randf() * TWO_PI_F;
                int new_idx = -1;
                if (g_build_type == BODY_SAT)
                    new_idx = create_body(BODY_SAT, "Satellite", hsl_to_color(160, 100, 50), 3.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
                else if (g_build_type == BODY_MINER)
                    new_idx = create_body(BODY_MINER, "Mining Station", hsl_to_color(212, 100, 97), 3.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
                else if (g_build_type == BODY_PLATFORM) {
                    new_idx = create_body(BODY_PLATFORM, get_build_name(g_build_type, g_build_wpn), hsl_to_color(33, 100, 50), 4.0f, 0, 0, g_build_parent, g_build_radius, 0.01f, ang);
                    set_platform_weapon(new_idx, g_build_wpn, 1);
                }
                if (new_idx >= 0) {
                    g_minerals -= (float)g_build_cost;
                    g_selected_idx = new_idx;
                    audio_play_sfx(&g_snd_select, 1);
                }
                g_build_active = 0;
            } else if (tx >= 246.0f && tx <= 304.0f && ty >= 125.0f && ty <= 159.0f) {
                g_build_active = 0;
                audio_play_sfx(&g_snd_select, 1);
            }
        } else {
            /* Upgrade Weapon Button */
            if (g_selected_idx >= 0 && g_bodies[g_selected_idx].active) {
                Body *b = &g_bodies[g_selected_idx];
                if (b->type == BODY_PLATFORM && b->has_weapon &&
                    tx >= 184.0f && tx <= 302.0f && ty >= 78.0f && ty <= 112.0f) {
                    int upg_cost = 75 * b->wpn_level;
                    if (g_minerals >= (float)upg_cost) {
                        g_minerals -= (float)upg_cost;
                        b->wpn_level++;
                        set_status("Upgraded weapon platform!");
                        audio_play_sfx(&g_snd_select, 1);
                    } else {
                        set_status("Need more minerals to upgrade!");
                    }
                }
            }
            /* Audio Mute Toggle */
            if (tx >= 184.0f && tx <= 302.0f && ty >= 126.0f && ty <= 158.0f) {
                g_music_muted = !g_music_muted;
                g_sfx_muted = g_music_muted;
                if (g_ndsp_ok) {
                    float mix[12] = {0};
                    mix[0] = g_music_muted ? 0.0f : 0.55f;
                    mix[1] = g_music_muted ? 0.0f : 0.55f;
                    ndspChnSetMix(0, mix);
                }
            }
        }
    }

    /* Smooth camera & zoom interpolation (`z.update`) */
    g_zoom += (g_target_zoom - g_zoom) * 0.2f;
    g_tilt = clampf(1.0f + (g_zoom - 0.1f), 1.0f, 1.6f);
    g_cam_x += (g_cam_tx - g_cam_x) * 0.2f;
    g_cam_y += (g_cam_ty - g_cam_y) * 0.2f;
}

int main(int argc, char *argv[]) {
    (void)argc; (void)argv;
    srand(0x3D5E70);

    romfsInit();
    gfxInitDefault();
    C3D_Init(C3D_DEFAULT_CMDBUF_SIZE);
    C2D_Init(C2D_DEFAULT_MAX_OBJECTS);
    C2D_Prepare();

    C3D_RenderTarget *top = C2D_CreateScreenTarget(GFX_TOP, GFX_LEFT);
    C3D_RenderTarget *bot = C2D_CreateScreenTarget(GFX_BOTTOM, GFX_LEFT);
    g_text_buf = C2D_TextBufNew(2048);

    /* Initialize starfield */
    for (int i = 0; i < 180; i++) {
        g_stars[i].x = randf() * TOP_W;
        g_stars[i].y = randf() * TOP_H;
        g_stars[i].color = hsl_to_color(randf() * 360.0f, 100.0f, 88.0f);
    }

    audio_init();
    init_solar_system();

    while (aptMainLoop()) {
        handle_input();
        if (hidKeysDown() & KEY_START && g_state != 0) {
            break; /* Clean exit to 3DS HOME Menu */
        }

        update_simulation();

        C2D_TextBufClear(g_text_buf);
        C3D_FrameBegin(C3D_FRAME_SYNCDRAW);

        C2D_TargetClear(top, MAKE_COLOR(8, 14, 24, 255));
        C2D_SceneBegin(top);
        render_top_screen();

        C2D_TargetClear(bot, MAKE_COLOR(14, 20, 34, 255));
        C2D_SceneBegin(bot);
        render_bottom_screen();

        C3D_FrameEnd(0);
    }

    audio_cleanup();
    C2D_TextBufDelete(g_text_buf);
    C2D_Fini();
    C3D_Fini();
    gfxExit();
    romfsExit();
    return 0;
}
