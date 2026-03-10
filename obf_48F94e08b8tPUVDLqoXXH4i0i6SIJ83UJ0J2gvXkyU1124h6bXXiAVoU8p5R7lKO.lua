-- ================================================================
-- LIGHTS HUB  V13.2  |  Blade Ball Auto-Parry
-- ================================================================
-- TIMING FIXES (vs V13):
--   • VEL_EMA  0.25 → 0.45   EMA tracks speed changes 2× faster
--   • SPEED_REF 260 → 200    Lead bonus kicks in at lower speeds
--   • LEAD_MAX 70ms → 100ms  More lead time at high ball speeds
--   • SPIKE_THRESH 70 → 40   Re-seeds EMA on smaller speed jumps
--   • DIRECTIONAL TTR        Uses approach-speed projection instead
--                             of raw dist/speed — no more TTR spikes
--                             when the ball changes direction
--   • PING COMPENSATION      Subtracts half round-trip ping from TTR
--                             so FireServer arrives on time, not late
--   • IsParried RESETS       Now resets on miss AND on timeout
--   • BETTER VELOCITY        LinearVelocity child first, Assembly fallback
--   • EMA PRE-WARM           EMAs seeded on ball bind, frame-1 accurate
-- NEW (V13.2):
--   • ANTI-CURVE GATE        (see inline comments)
--   • FIRE_DELAY_OFFSET      Subtracts 175ms from the effective fire window
--                             so the parry clicks ~175ms later than default.
--                             Tune at the top of TIMING CONSTANTS.
-- PING FIXES (V13.2a):
--   • THROTTLED READS        Ping polled every 0.75 s instead of every frame
--                             (~60× less Stats API overhead, far less noise)
--   • SPIKE REJECTION        Samples > 2.5× current EMA are capped before
--                             blending, so packet-loss spikes are absorbed
--   • DUAL EMA               smoothPing (fast, α=0.20) drives the HUD display
--                             stablePing (slow, α=0.04) drives timing decisions
--                             so a network hiccup cannot cause a premature fire
-- FIRST-TARGET PRECLICK FIX (V13.2b):
--   • ACQUIRE DELAY          All fire paths (including emergency) are blocked
--                             for ACQUIRE_DELAY (100 ms) after the ball first
--                             targets the player, giving the EMA time to settle
--   • APPROACH RE-SEED       Target-change handler now re-seeds smoothApproach
--                             to the real closure rate instead of zeroing it,
--                             preventing the EMA from rushing 0→real and making
--                             TTR swing wildly on the first few frames
--   Parry method: original V13 (FireServer + :Fire() + VIM fallback)
-- ================================================================

if _G.LH13_Cleanup then _G.LH13_Cleanup() end

local RunService       = game:GetService("RunService")
local Players          = game:GetService("Players")
local VIM              = game:GetService("VirtualInputManager")
local UserInputService = game:GetService("UserInputService")
local CoreGui          = game:GetService("CoreGui")
local RS               = game:GetService("ReplicatedStorage")

local Player = Players.LocalPlayer
local Balls  = workspace:WaitForChild("Balls", 9000000000)

local ParryRemote = nil
pcall(function()
    local remotes = RS:WaitForChild("Remotes", 4)
    ParryRemote   = remotes:WaitForChild("ParryButtonPress", 4)
end)

-- ================================================================
-- TIMING CONSTANTS
-- ================================================================
local BASE_RADIUS    = 13
local BASE_WINDOW    = 0.27   -- starting fire window (270 ms floor)
local COOLDOWN       = 0.5

local WIN_MIN        = 0.27   -- never drop below 270 ms
local WIN_MAX        = 1   -- no practical ceiling — grows until it parries
local WIN_STEP_MISS  = 0.01
local WIN_STEP_HIT   = 0.004
local OUTCOME_WIN    = 0.8

local FIRE_DELAY_OFFSET = 0.175  -- delays effective fire by 175 ms (tune as needed)

-- ── Speed-adaptive window ─────────────────────────────────────────
local VEL_EMA        = 0.45
local SPEED_REF      = 200
local LEAD_MAX       = 0.1

local JITTER_THRESH  = 200
local JITTER_RANGE   = 100
local JITTER_MAX     = 0.025

-- ── Curve compensation ────────────────────────────────────────────
local KAPPA_EMA      = 0.3
local CURVE_BONUS    = 0.04
local KAPPA_MAX      = 0.06

-- ── Anti-curve gate ───────────────────────────────────────────────
local CURVE_GATE_FRAC  = 0.2
local CURVE_ALIGN_MIN  = 0.55
local CURVE_ALIGN_EMER = 0.28

-- ── Straight-ball early-fire bonus ────────────────────────────────
local STRAIGHT_BONUS = 0.1

-- ── Bounty spike detection ────────────────────────────────────────
local SPIKE_THRESH   = 40
local SPIKE_HOLD     = 1.2

local EMERG_MULT     = 1.5
local EMERG_BD_MULT  = 1.9

-- ── Ping compensation ─────────────────────────────────────────────
local PING_EMA        = 0.2   -- fast EMA for HUD display
local PING_STABLE_EMA = 0.04   -- slow EMA used for timing decisions (spike-resistant)
local PING_FLOOR      = 0.005
local PING_CEIL       = 0.2
local PING_SPIKE_MULT = 2.5    -- reject samples > 2.5× current smooth (spike guard)
local PING_READ_RATE  = 0.75   -- only poll the network stat every 0.75 s

-- ── First-target acquisition guard ────────────────────────────────
-- After the ball switches target to us, block ALL fire paths for this
-- many seconds so the approach-speed EMA can stabilise before any
-- timing decision is made.  Prevents preclicks when the ball was
-- already nearby at the moment of targeting.
local ACQUIRE_DELAY   = 0.1   -- 100 ms hold-off (tune down if reaction feels slow)

-- ================================================================
-- STATE
-- ================================================================
local autoOn        = false
local IsParried     = false
local Connection    = nil
local fireCount     = 0
local lastParryTime = 0
local _connections  = {}

local liveWindow    = BASE_WINDOW
local liveRadius    = BASE_RADIUS
local pendingParry  = nil

local targetAcquiredAt = 0   -- tick() when ball last switched target to us

local prevVel, prevTime = nil, nil
local smoothKappa       = 0
local smoothNormal      = Vector3.new(0, 0, 0)

local smoothSpeed    = 0
local smoothApproach = 0

local bdHighlight    = false
local bdSpike        = false
local bdSpikeUntil   = 0
local bdActive       = false

local smoothPing     = 0.02  -- fast EMA, used for HUD display
local stablePing     = 0.02  -- slow spike-resistant EMA, used for timing
local lastPingRead   = 0      -- throttle: tracks last hardware poll time

local dbDist       = 0
local dbSpeed      = 0
local dbTTR        = 99
local dbFW         = BASE_WINDOW
local dbTarget     = false
local dbFrozen     = false
local dbStatus     = "IDLE"
local dbAlign      = 1
local dbCurveGated = false
local dbAbility    = "—"
local dbAbilityTag = ""

-- ================================================================
-- ABILITY AWARENESS SYSTEM
-- ================================================================
local AB = { SUPPRESS="SUPPRESS", FROZEN="FROZEN",
             PULL="PULL", TELEPORT="TELEPORT", NONE="NONE" }

local ABILITY_DB = {
    ["forcefield"]           = AB.SUPPRESS,
    ["infinity"]             = AB.SUPPRESS,
    ["flash counter"]        = AB.SUPPRESS,
    ["rapture"]              = AB.SUPPRESS,
    ["singularity"]          = AB.SUPPRESS,
    ["death slash"]          = AB.SUPPRESS,
    ["slashes of fury"]      = AB.SUPPRESS,
    ["invisibility"]         = AB.SUPPRESS,
    ["absolute confidence"]  = AB.SUPPRESS,
    ["guardian angel"]       = AB.SUPPRESS,
    ["dragon spirit"]        = AB.SUPPRESS,
    ["doppelganger"]         = AB.SUPPRESS,
    ["decrypted clone"]      = AB.SUPPRESS,
    ["serpent shadow clone"] = AB.SUPPRESS,
    ["necromancer"]          = AB.SUPPRESS,

    ["freeze"]               = AB.FROZEN,
    ["telekinesis"]          = AB.FROZEN,
    ["freeze trap"]          = AB.FROZEN,
    ["time hole"]            = AB.FROZEN,
    ["quantum arena"]        = AB.FROZEN,

    ["pull"]                 = AB.PULL,
    ["hell hook"]            = AB.PULL,
    ["gale's edge"]          = AB.PULL,

    ["dash"]                 = AB.TELEPORT,
    ["thunder dash"]         = AB.TELEPORT,
    ["shadow step"]          = AB.TELEPORT,
    ["blink"]                = AB.TELEPORT,
    ["ninja dash"]           = AB.TELEPORT,
    ["waypoint"]             = AB.TELEPORT,
    ["swap"]                 = AB.TELEPORT,
    ["phase bypass"]         = AB.TELEPORT,
    ["bunny leap"]           = AB.TELEPORT,
    ["displace"]             = AB.TELEPORT,

    ["super jump"]           = AB.NONE,
    ["platform"]             = AB.NONE,
    ["quad jump"]            = AB.NONE,
    ["luck"]                 = AB.NONE,
    ["reaper"]               = AB.NONE,
    ["wind cloak"]           = AB.NONE,
    ["raging deflection"]    = AB.NONE,
    ["calming deflection"]   = AB.NONE,
    ["martyrdom"]            = AB.NONE,
    ["misfortune"]           = AB.NONE,
    ["scopophobia"]          = AB.NONE,
    ["virus"]                = AB.NONE,
    ["golden ball"]          = AB.NONE,
    ["aerodynamic slash"]    = AB.NONE,
    ["qi-charge"]            = AB.NONE,
    ["pulse"]                = AB.NONE,
    ["chieftain's totem"]    = AB.NONE,
    ["blade trap"]           = AB.NONE,
    ["force"]                = AB.NONE,
    ["phantom"]              = AB.NONE,
    ["tact"]                 = AB.NONE,
    ["bounty"]               = AB.NONE,
    ["continuity zero"]      = AB.NONE,
    ["fracture"]             = AB.NONE,
    ["quasar"]               = AB.NONE,
    ["slash of duality"]     = AB.NONE,
    ["titan blade"]          = AB.NONE,
    ["dribble"]              = AB.NONE,
}

local myAbilityName     = "unknown"
local myAbilityBehav    = AB.NONE
local abilityGated      = false
local teleportSkipUntil = 0
local lastHRPPos        = Vector3.zero
local ballFrozenSince   = 0
local pullActiveUntil   = 0

local TELEPORT_SKIP       = 0.3
local PULL_BONUS          = 0.08
local FROZEN_RESUME_BONUS = 0.06
local frozenWasActive     = false
local frozenResumeUntil   = 0

local COOLDOWN_ATTRS = {
    "AbilityCooldown","abilityCooldown","Cooldown","cooldown",
    "AbilityCD","abilityCD","CooldownTime","cooldownTime",
    "SkillCooldown","skillCooldown",
}

local suppressUntil = 0
local cdWatchConns  = {}

local function DisconnectCDWatchers()
    for _, c in ipairs(cdWatchConns) do pcall(function() c:Disconnect() end) end
    cdWatchConns = {}
end

local function OnCooldownChanged(char, attrName)
    if myAbilityBehav ~= AB.SUPPRESS then return end
    local v = char:GetAttribute(attrName)
    if type(v) == "number" and v > 0 then
        suppressUntil = tick() + math.max(v, 0.5)
        dbStatus = "[ABILITY ACTIVE]"
    end
end

local function WatchCooldowns(char)
    DisconnectCDWatchers()
    for _, attrName in ipairs(COOLDOWN_ATTRS) do
        local ok, conn = pcall(function()
            return char:GetAttributeChangedSignal(attrName):Connect(function()
                OnCooldownChanged(char, attrName)
            end)
        end)
        if ok and conn then cdWatchConns[#cdWatchConns + 1] = conn end
    end
    local ok2, conn2 = pcall(function()
        return char.AttributeChanged:Connect(function(attrName2)
            for _, k in ipairs(COOLDOWN_ATTRS) do
                if k == attrName2 then OnCooldownChanged(char, attrName2); break end
            end
        end)
    end)
    if ok2 and conn2 then cdWatchConns[#cdWatchConns + 1] = conn2 end
end

local ATTR_NAMES = {
    "ability","Ability","equippedAbility","EquippedAbility",
    "skill","Skill","AbilityName","SkillName","currentAbility",
}
local SV_NAMES = {
    "AbilityName","Ability","AbilityValue","SkillName","EquippedAbility",
}

local function DetectAbilityName(char)
    if not char then return nil end
    for _, k in ipairs(ATTR_NAMES) do
        local v = char:GetAttribute(k)
        if type(v) == "string" and #v > 0 then return v:lower() end
    end
    for _, k in ipairs(SV_NAMES) do
        local sv = char:FindFirstChild(k)
        if sv and sv:IsA("StringValue") and #sv.Value > 0 then
            return sv.Value:lower()
        end
    end
    return nil
end

local function RefreshAbility(char)
    local name = DetectAbilityName(char)
    if name then
        myAbilityName  = name
        myAbilityBehav = ABILITY_DB[name] or AB.NONE
        dbAbility      = name
        dbAbilityTag   = myAbilityBehav ~= AB.NONE and ("[" .. myAbilityBehav .. "]") or ""
    end
    if char then WatchCooldowns(char) end
end

-- ================================================================
-- BALL VELOCITY
-- ================================================================
local _velSrcName = nil

local function GetBallVelocity(ball)
    if not ball or not ball.Parent then return Vector3.zero end
    if _velSrcName then
        local src = ball:FindFirstChild(_velSrcName)
        if src then
            if src.VectorVelocity then return src.VectorVelocity end
            if src:IsA("BodyVelocity") then return src.Velocity end
        end
    end
    for _, child in ipairs(ball:GetChildren()) do
        if child:IsA("LinearVelocity") then
            _velSrcName = child.Name; return child.VectorVelocity
        end
        if child:IsA("BodyVelocity") then
            _velSrcName = child.Name; return child.Velocity
        end
    end
    local ok, vel = pcall(function() return ball.AssemblyLinearVelocity end)
    if ok and vel then return vel end
    return Vector3.zero
end

-- ================================================================
-- ABILITY GATE
-- ================================================================
local function CheckAbilityGate(char, ball, now)
    if myAbilityBehav == AB.NONE then abilityGated = false; return false end

    if myAbilityBehav == AB.SUPPRESS then
        if now < suppressUntil then abilityGated = true; return true end
        if char:GetAttribute("abilityActive")   == true
        or char:GetAttribute("AbilityActive")   == true
        or char:GetAttribute("isAbilityActive") == true then
            suppressUntil = now + 0.5; abilityGated = true; return true
        end
        for _, d in ipairs(char:GetChildren()) do
            local ln = d.Name:lower()
            if ln:find("forcefield") or ln:find("shield")
            or ln:find("singularity") or ln:find("infinity")
            or ln:find("invisible") then
                suppressUntil = now + 0.5; abilityGated = true; return true
            end
            if d:IsA("SelectionBox") or d:IsA("Highlight") then
                suppressUntil = now + 0.5; abilityGated = true; return true
            end
        end
        local hrp = char:FindFirstChild("HumanoidRootPart")
        if hrp and hrp.Transparency >= 0.7 then
            suppressUntil = now + 0.5; abilityGated = true; return true
        end
        abilityGated = false; return false
    end

    if myAbilityBehav == AB.FROZEN then
        local spd = ball and ball.Parent and GetBallVelocity(ball).Magnitude or 999
        if spd < 0.8 then
            if ballFrozenSince == 0 then ballFrozenSince = now end
            local isFrozen = now - ballFrozenSince > 0.1
            if isFrozen then frozenWasActive = true end
            abilityGated = isFrozen; return isFrozen
        else
            ballFrozenSince = 0
            if frozenWasActive then
                frozenWasActive = false; frozenResumeUntil = now + 0.35
            end
            abilityGated = false; return false
        end
    end

    if myAbilityBehav == AB.PULL then abilityGated = false; return false end

    if myAbilityBehav == AB.TELEPORT then
        if now < teleportSkipUntil then abilityGated = true; return true end
        abilityGated = false; return false
    end

    abilityGated = false; return false
end

-- ================================================================
-- PARRY
-- ================================================================
local function Parry()
    if ParryRemote then
        pcall(function() ParryRemote:FireServer() end)
        pcall(function() ParryRemote:Fire() end)
    end
    pcall(function() VIM:SendMouseButtonEvent(0, 0, 0, true,  game, 0) end)
    pcall(function() VIM:SendMouseButtonEvent(0, 0, 0, false, game, 0) end)
end

local function DoParry(ball, ttr)
    IsParried     = true
    lastParryTime = tick()
    fireCount    += 1
    dbStatus      = "FIRED"
    local char = Player.Character
    local hum  = char and char:FindFirstChildOfClass("Humanoid")
    pendingParry = {
        time_     = tick(),
        preHealth = hum and hum.Health or math.huge,
        ttr       = ttr or 0,
        ball      = ball,
        until_    = tick() + OUTCOME_WIN,
    }
    Parry()
end

-- ================================================================
-- ADAPTIVE TIMING
-- ================================================================
local function PollOutcome()
    if not pendingParry then return end
    local now = tick()
    local pp  = pendingParry
    local char = Player.Character
    local hum  = char and char:FindFirstChildOfClass("Humanoid")

    if hum and hum.Health < pp.preHealth - 1 then
        liveWindow   = math.min(WIN_MAX, liveWindow + WIN_STEP_MISS)
        liveRadius   = math.min(BASE_RADIUS + 3, liveRadius + 0.3)
        IsParried    = false
        dbStatus     = "MISS↑"
        pendingParry = nil
        return
    end

    local ball = pp.ball
    if ball and ball.Parent and ball:GetAttribute("target") ~= Player.Name then
        liveWindow   = math.max(WIN_MIN, liveWindow - WIN_STEP_HIT)
        dbStatus     = "HIT✓"
        pendingParry = nil
        return
    end

    if now > pp.until_ then
        IsParried    = false
        dbStatus     = "—"
        pendingParry = nil
    end
end

-- ================================================================
-- CURVE DETECTION
-- ================================================================
local function ResetCurve()
    prevVel, prevTime = nil, nil
    smoothKappa  = 0
    smoothNormal = Vector3.new(0, 0, 0)
end

local function UpdateCurve(vel, now)
    if not prevVel then prevVel = vel; prevTime = now; return end
    local dt = now - prevTime
    if dt < 0.0001 then return end
    local accel = (vel - prevVel) / dt
    prevVel, prevTime = vel, now
    local spd = vel.Magnitude
    if spd < 2 then ResetCurve(); return end
    local u    = vel / spd
    local aN   = accel - u * accel:Dot(u)
    local kRaw = vel:Cross(accel).Magnitude / (spd ^ 3)
    smoothKappa  = smoothKappa  + KAPPA_EMA * (kRaw - smoothKappa)
    smoothNormal = smoothNormal + (aN - smoothNormal) * 0.25
end

local function PredictPos(pos, vel, t)
    return pos + vel * t + 0.5 * smoothNormal * (t * t)
end

-- ================================================================
-- BOUNTY DETECTION
-- ================================================================
local function UpdateBounty(rawSpd, emaSpd, onTarget)
    local now = tick()
    if onTarget and (rawSpd - emaSpd) > SPIKE_THRESH then
        bdSpikeUntil = now + SPIKE_HOLD
    end
    bdSpike     = now < bdSpikeUntil
    local char  = Player.Character
    bdHighlight = char ~= nil and char:FindFirstChildWhichIsA("Highlight") ~= nil
    bdActive    = bdHighlight or bdSpike
end

-- ================================================================
-- VELOCITY BONUS
-- ================================================================
local function VelBonus(spd)
    local lead   = math.clamp(spd / SPEED_REF, 0, 1) * LEAD_MAX
    local jitter = math.clamp((spd - JITTER_THRESH) / JITTER_RANGE, 0, 1) * JITTER_MAX
    return lead + jitter
end

-- ================================================================
-- PING TRACKING
-- ================================================================
local function UpdatePing()
    -- Throttle: only poll the network hardware every PING_READ_RATE seconds.
    -- Polling every Heartbeat (~60 fps) produces noisy burst readings that
    -- feed spikes straight into the timing logic.
    local now = tick()
    if now - lastPingRead < PING_READ_RATE then return end
    lastPingRead = now

    local raw = 0
    pcall(function()
        raw = game:GetService("Stats").Network.ServerStatsItem["Data Ping"]:GetValue() / 1000
    end)
    if raw == 0 then pcall(function() raw = Player:GetNetworkPing() end) end
    if raw <= 0 then return end

    -- Spike rejection: cap the input at PING_SPIKE_MULT × current smooth so a
    -- single anomalous sample (packet loss, GC pause) cannot yank the EMA far.
    local cap = smoothPing * PING_SPIKE_MULT
    if cap < PING_FLOOR * PING_SPIKE_MULT then cap = PING_FLOOR * PING_SPIKE_MULT end
    raw = math.min(raw, cap)
    raw = math.clamp(raw, PING_FLOOR, PING_CEIL)

    -- Fast EMA  → HUD display (responsive)
    smoothPing = smoothPing + PING_EMA * (raw - smoothPing)
    smoothPing = math.clamp(smoothPing, PING_FLOOR, PING_CEIL)

    -- Slow EMA  → timing decisions (stable, spike-resistant)
    stablePing = stablePing + PING_STABLE_EMA * (raw - stablePing)
    stablePing = math.clamp(stablePing, PING_FLOOR, PING_CEIL)
end

-- ================================================================
-- HELPERS
-- ================================================================
local function GetBall()
    for _, b in ipairs(Balls:GetChildren()) do
        if b:GetAttribute("realBall") == true then return b end
    end
end

local function IsAlive()
    local c = Player.Character
    if not c then return false end
    local h = c:FindFirstChildOfClass("Humanoid")
    return h and h.Health > 0
end

local function SeedEMAs(ball, hrp)
    if not (ball and hrp) then return end
    local vel      = GetBallVelocity(ball)
    local rawSpd   = vel.Magnitude
    smoothSpeed    = rawSpd
    local toPlayer = hrp.Position - ball.Position
    smoothApproach = toPlayer.Magnitude > 0
        and math.max(0, toPlayer.Unit:Dot(vel))
        or  rawSpd
end

local function ConnectBall(ball)
    if Connection then Connection:Disconnect(); Connection = nil end
    IsParried         = false
    pendingParry      = nil
    _velSrcName       = nil
    ResetCurve()
    smoothSpeed       = 0
    smoothApproach    = 0
    ballFrozenSince   = 0
    frozenWasActive   = false
    frozenResumeUntil = 0
    local char = Player.Character
    local hrp  = char and char:FindFirstChild("HumanoidRootPart")
    SeedEMAs(ball, hrp)
    Connection = ball:GetAttributeChangedSignal("target"):Connect(function()
        IsParried = false
        -- Re-seed smoothApproach to the real closure rate instead of zeroing it.
        -- Zeroing causes the EMA to rush from 0 upward, making TTR swing
        -- wildly for the first few frames and tripping the fire window early.
        local c2  = Player.Character
        local h2  = c2 and c2:FindFirstChild("HumanoidRootPart")
        if h2 and ball.Parent then
            local v2   = GetBallVelocity(ball)
            local toP  = h2.Position - ball.Position
            smoothApproach = toP.Magnitude > 0
                and math.max(0, toP.Unit:Dot(v2)) or v2.Magnitude
        else
            smoothApproach = 0
        end
        -- Only stamp the acquire time when it's actually our turn
        if ball:GetAttribute("target") == Player.Name then
            targetAcquiredAt = tick()
        end
    end)
end

for _, b in ipairs(Balls:GetChildren()) do
    if b:GetAttribute("realBall") then ConnectBall(b) end
end

_connections[#_connections+1] = Balls.ChildAdded:Connect(function(b)
    task.wait()
    if b:GetAttribute("realBall") then ConnectBall(b) end
end)

_connections[#_connections+1] = Balls.ChildRemoved:Connect(function()
    IsParried = false; pendingParry = nil; _velSrcName = nil
    ResetCurve(); smoothSpeed = 0; smoothApproach = 0
    ballFrozenSince = 0; frozenWasActive = false; frozenResumeUntil = 0
    if Connection then Connection:Disconnect(); Connection = nil end
end)

_connections[#_connections+1] = Player.CharacterAdded:Connect(function(char)
    DisconnectCDWatchers(); suppressUntil = 0
    task.wait(1)
    RefreshAbility(char)
    lastHRPPos = Vector3.zero
end)

do
    local char = Player.Character
    if char then
        RefreshAbility(char)
        local hrp = char:FindFirstChild("HumanoidRootPart")
        if hrp then lastHRPPos = hrp.Position end
    end
end

-- ================================================================
-- CORE LOOP
-- ================================================================
_connections[#_connections+1] = RunService.PreSimulation:Connect(function()
    local ball = GetBall()
    local char = Player.Character
    local hrp  = char and char:FindFirstChild("HumanoidRootPart")
    if not (ball and hrp) then return end

    local vel    = GetBallVelocity(ball)
    local now    = tick()
    local rawSpd = vel.Magnitude

    smoothSpeed = smoothSpeed + VEL_EMA * (rawSpd - smoothSpeed)

    local toPlayer    = hrp.Position - ball.Position
    local rawApproach = toPlayer.Magnitude > 0
        and math.max(0, toPlayer.Unit:Dot(vel)) or 0
    smoothApproach = smoothApproach + VEL_EMA * (rawApproach - smoothApproach)

    dbSpeed  = rawSpd
    dbDist   = (ball.Position - hrp.Position).Magnitude
    dbTarget = ball:GetAttribute("target") == Player.Name
    dbFrozen = dbTarget and rawSpd < 1

    UpdateBounty(rawSpd, smoothSpeed, dbTarget)

    if bdActive and (rawSpd - smoothSpeed) > SPIKE_THRESH then
        smoothSpeed = rawSpd; smoothApproach = rawApproach
    end

    if rawSpd >= 2 then UpdateCurve(vel, now) else ResetCurve() end

    local curveFrac   = math.clamp(smoothKappa / KAPPA_MAX, 0, 1)
    local bountyBonus = bdActive and 0.06 or 0
    local radExtra    = bdActive and 2   or 0
    local emergMult   = bdActive and EMERG_BD_MULT or EMERG_MULT

    local radius = liveRadius + radExtra
    local emergD = radius * emergMult
    local apSkip = radius * 3

    local alignFrac = smoothSpeed > 1
        and math.clamp(smoothApproach / smoothSpeed, 0, 1) or 1
    dbAlign = alignFrac

    -- Use stablePing (slow, spike-resistant EMA) for all timing math so a
    -- momentary network hiccup cannot cause a premature or missed parry.
    local halfPing = stablePing * 0.5

    local pullBonus = (myAbilityBehav == AB.PULL and dbTarget) and PULL_BONUS or 0
    local frBonus   = (now < frozenResumeUntil) and FROZEN_RESUME_BONUS or 0

    local effectiveFireWin = math.min(0.33, liveWindow
                           + VelBonus(smoothApproach)
                           + halfPing
                           + pullBonus
                           + frBonus
                           - FIRE_DELAY_OFFSET)

    dbTTR = smoothApproach > 1
        and math.max(0, (dbDist - radius) / smoothApproach) - halfPing
        or  99

    dbFW = effectiveFireWin   -- HUD reflects the actual window in use

    -- ── Gate checks ───────────────────────────────────────────────
    if not autoOn              then return end
    if not IsAlive()           then return end
    if not dbTarget            then return end
    if now - lastParryTime < COOLDOWN then return end
    if IsParried               then return end

    -- Acquisition guard: block all fire paths for ACQUIRE_DELAY seconds
    -- after the ball first targets us.  The approach-speed EMA needs a
    -- few frames to settle; firing before it does causes preclicks.
    if now - targetAcquiredAt < ACQUIRE_DELAY then return end

    -- Frozen / emergency paths fire immediately
    if dbFrozen             then DoParry(ball, 0); return end
    if dbDist <= emergD     then DoParry(ball, 0); return end

    if dbDist > apSkip then
        if (hrp.Position - ball.Position):Dot(vel) <= 0 then return end
    end

    -- Main timing gate — velocity-tuned, fires when TTR ≤ window
    if dbTTR > effectiveFireWin then return end

    local predDist = (PredictPos(ball.Position, vel, effectiveFireWin) - hrp.Position).Magnitude
    if predDist > radius * 4 then return end

    -- Anti-curve gate
    if curveFrac > CURVE_GATE_FRAC then
        local thresh = dbDist <= emergD * 1.5 and CURVE_ALIGN_EMER or CURVE_ALIGN_MIN
        dbCurveGated = alignFrac < thresh
        if dbCurveGated then return end
    else
        dbCurveGated = false
    end

    if CheckAbilityGate(char, ball, now) then
        dbStatus = "[" .. myAbilityBehav .. "]"; return
    end

    DoParry(ball, dbTTR)
end)

_connections[#_connections+1] = UserInputService.InputBegan:Connect(function(inp, gpe)
    if not gpe and inp.KeyCode == Enum.KeyCode.E then Parry() end
end)

-- ================================================================
-- CLEANUP
-- ================================================================
_G.LH13_Cleanup = function()
    for _, c in ipairs(_connections) do pcall(function() c:Disconnect() end) end
    if Connection then pcall(function() Connection:Disconnect() end) end
    DisconnectCDWatchers()
    if CoreGui:FindFirstChild("LH13") then CoreGui.LH13:Destroy() end
    _G.LH13_Cleanup = nil
end

-- ================================================================
-- GUI
-- ================================================================
if CoreGui:FindFirstChild("LH13") then CoreGui.LH13:Destroy() end

local BG = Color3.fromRGB(9,   8,  14)
local S1 = Color3.fromRGB(18,  15,  26)
local S2 = Color3.fromRGB(24,  20,  36)
local AC = Color3.fromRGB(100, 42, 210)
local GN = Color3.fromRGB(42,  196,  98)
local RD = Color3.fromRGB(212,  44,  44)
local YL = Color3.fromRGB(212, 182,  28)
local OR = Color3.fromRGB(220, 120,  20)
local CY = Color3.fromRGB(34,  188, 212)
local T0 = Color3.fromRGB(222, 213, 237)
local T1 = Color3.fromRGB(138, 122, 163)
local T2 = Color3.fromRGB(62,   55,  86)
local DM = Color3.fromRGB(36,   32,  52)
local TL = Color3.fromRGB(28,  160, 140)

local function corner(f, r)
    Instance.new("UICorner", f).CornerRadius = UDim.new(0, r or 6)
end
local function stroke(f, c)
    local s = Instance.new("UIStroke", f)
    s.Color = c or DM; s.Thickness = 1
    s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
end

local Scr = Instance.new("ScreenGui", CoreGui)
Scr.Name = "LH13"; Scr.ResetOnSpawn = false
Scr.IgnoreGuiInset = true; Scr.ZIndexBehavior = Enum.ZIndexBehavior.Sibling

local Win = Instance.new("Frame", Scr)
Win.Size = UDim2.new(0, 188, 0, 0); Win.AutomaticSize = Enum.AutomaticSize.Y
Win.Position = UDim2.new(0, 16, 0, 16)
Win.BackgroundColor3 = BG; Win.BorderSizePixel = 0
Win.Active = true; Win.Draggable = true
corner(Win, 8); stroke(Win, S2)

local WList = Instance.new("UIListLayout", Win)
WList.SortOrder = Enum.SortOrder.LayoutOrder
WList.HorizontalAlignment = Enum.HorizontalAlignment.Center

local TBar = Instance.new("Frame", Win)
TBar.Size = UDim2.new(1, 0, 0, 30)
TBar.BackgroundColor3 = S1; TBar.BorderSizePixel = 0; TBar.LayoutOrder = 0
corner(TBar, 8)

local TCapFill = Instance.new("Frame", TBar)
TCapFill.Size = UDim2.new(1, 0, 0.5, 0); TCapFill.Position = UDim2.new(0, 0, 0.5, 0)
TCapFill.BackgroundColor3 = S1; TCapFill.BorderSizePixel = 0; TCapFill.ZIndex = 2

local Stripe = Instance.new("Frame", TBar)
Stripe.Size = UDim2.new(0, 3, 1, -10); Stripe.Position = UDim2.new(0, 0, 0, 5)
Stripe.BackgroundColor3 = AC; Stripe.BorderSizePixel = 0; Stripe.ZIndex = 3; corner(Stripe, 2)

local tTitle = Instance.new("TextLabel", TBar)
tTitle.Position = UDim2.new(0, 9, 0, 4); tTitle.Size = UDim2.new(0.74, 0, 0, 12)
tTitle.BackgroundTransparency = 1; tTitle.Text = "LIGHTS HUB  V13.2"
tTitle.TextColor3 = T0; tTitle.Font = Enum.Font.GothamBold; tTitle.TextSize = 9
tTitle.TextXAlignment = Enum.TextXAlignment.Left; tTitle.ZIndex = 3

local tSub = Instance.new("TextLabel", TBar)
tSub.Position = UDim2.new(0, 9, 0, 17); tSub.Size = UDim2.new(0.74, 0, 0, 9)
tSub.BackgroundTransparency = 1; tSub.Text = "Blade Ball · Auto Parry"
tSub.TextColor3 = T2; tSub.Font = Enum.Font.Gotham; tSub.TextSize = 7
tSub.TextXAlignment = Enum.TextXAlignment.Left; tSub.ZIndex = 3

local MinB = Instance.new("TextButton", TBar)
MinB.Size = UDim2.new(0, 16, 0, 16); MinB.Position = UDim2.new(1, -21, 0.5, -8)
MinB.BackgroundColor3 = BG; MinB.Text = "−"; MinB.TextColor3 = T1
MinB.Font = Enum.Font.GothamBold; MinB.TextSize = 10; MinB.BorderSizePixel = 0; MinB.ZIndex = 4
corner(MinB, 4)

local Body = Instance.new("Frame", Win)
Body.Size = UDim2.new(1, 0, 0, 0); Body.AutomaticSize = Enum.AutomaticSize.Y
Body.BackgroundTransparency = 1; Body.LayoutOrder = 1
local BList = Instance.new("UIListLayout", Body)
BList.Padding = UDim.new(0, 2); BList.SortOrder = Enum.SortOrder.LayoutOrder
BList.HorizontalAlignment = Enum.HorizontalAlignment.Center
local BPad = Instance.new("UIPadding", Body)
BPad.PaddingTop    = UDim.new(0, 6); BPad.PaddingBottom = UDim.new(0, 8)
BPad.PaddingLeft   = UDim.new(0, 7); BPad.PaddingRight  = UDim.new(0, 7)

local bodyOpen = true
MinB.MouseButton1Click:Connect(function()
    bodyOpen = not bodyOpen; Body.Visible = bodyOpen
    MinB.Text = bodyOpen and "−" or "+"
end)

_connections[#_connections+1] = UserInputService.InputBegan:Connect(function(i, g)
    if not g and i.KeyCode == Enum.KeyCode.LeftControl then Win.Visible = not Win.Visible end
end)

local lo = 0
local function LO() lo += 1; return lo end

local function Div()
    local f = Instance.new("Frame", Body)
    f.Size = UDim2.new(1, 0, 0, 1); f.BackgroundColor3 = S2
    f.BorderSizePixel = 0; f.LayoutOrder = LO()
end

local function Tog(lbl, getter, setter, ac)
    ac = ac or AC
    local btn = Instance.new("TextButton", Body)
    btn.Size = UDim2.new(1, 0, 0, 24); btn.BackgroundColor3 = S2
    btn.BorderSizePixel = 0; btn.Text = ""; btn.LayoutOrder = LO()
    corner(btn, 5); stroke(btn, DM)
    local pill = Instance.new("Frame", btn)
    pill.Size = UDim2.new(0, 24, 0, 12); pill.Position = UDim2.new(1, -31, 0.5, -6)
    pill.BackgroundColor3 = BG; pill.BorderSizePixel = 0; corner(pill, 6)
    local knob = Instance.new("Frame", pill)
    knob.Size = UDim2.new(0, 8, 0, 8); knob.Position = UDim2.new(0, 2, 0.5, -4)
    knob.BackgroundColor3 = T2; knob.BorderSizePixel = 0; corner(knob, 4)
    local lT = Instance.new("TextLabel", btn)
    lT.Size = UDim2.new(1, -44, 1, 0); lT.Position = UDim2.new(0, 8, 0, 0)
    lT.BackgroundTransparency = 1; lT.Text = lbl; lT.TextColor3 = T1
    lT.Font = Enum.Font.Gotham; lT.TextSize = 9; lT.TextXAlignment = Enum.TextXAlignment.Left
    local str = Instance.new("UIStroke", btn)
    str.Thickness = 1; str.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
    local function R()
        local on = getter()
        pill.BackgroundColor3 = on and ac or BG
        knob.BackgroundColor3 = on and T0 or T2
        knob.Position         = on and UDim2.new(1, -10, 0.5, -4) or UDim2.new(0, 2, 0.5, -4)
        str.Color             = on and ac or DM
        lT.TextColor3         = on and T0 or T1
    end
    R()
    btn.MouseButton1Click:Connect(function() setter(not getter()); R() end)
    return R
end

local function Row(lbl)
    local f = Instance.new("Frame", Body)
    f.Size = UDim2.new(1, 0, 0, 13); f.BackgroundTransparency = 1; f.LayoutOrder = LO()
    local l = Instance.new("TextLabel", f)
    l.Size = UDim2.new(0.55, 0, 1, 0); l.BackgroundTransparency = 1
    l.Text = lbl; l.TextColor3 = T2
    l.Font = Enum.Font.Gotham; l.TextSize = 8; l.TextXAlignment = Enum.TextXAlignment.Left
    local v = Instance.new("TextLabel", f)
    v.Size = UDim2.new(0.45, 0, 1, 0); v.Position = UDim2.new(0.55, 0, 0, 0)
    v.BackgroundTransparency = 1; v.Text = "—"; v.TextColor3 = T0
    v.Font = Enum.Font.GothamBold; v.TextSize = 8; v.TextXAlignment = Enum.TextXAlignment.Right
    return v
end

local function ChipRow()
    local f = Instance.new("Frame", Body)
    f.Size = UDim2.new(1, 0, 0, 18); f.BackgroundTransparency = 1; f.LayoutOrder = LO()
    local function chip(ox, w)
        local bg = Instance.new("Frame", f)
        bg.Size = UDim2.new(0, w, 0, 14); bg.Position = UDim2.new(0, ox, 0.5, -7)
        bg.BackgroundColor3 = S2; bg.BorderSizePixel = 0; corner(bg, 4)
        local t = Instance.new("TextLabel", bg)
        t.Size = UDim2.new(1, 0, 1, 0); t.BackgroundTransparency = 1
        t.Font = Enum.Font.GothamBold; t.TextSize = 7; t.Text = "—"; t.TextColor3 = T2
        return t, bg
    end
    local c1, b1 = chip(0,   56)
    local c2, b2 = chip(62,  50)
    local c3, b3 = chip(118, 52)
    return c1, b1, c2, b2, c3, b3
end

Tog("Auto Parry", function() return autoOn end, function(v) autoOn = v end)
Div()
local rDist    = Row("Distance")
local rSpeed   = Row("Speed")
local rTTR     = Row("TTR (ping-adj)")
local rFW      = Row("Fire Window")
Div()
local rAdapt   = Row("Adapt Window")
local rPing    = Row("Ping EMA")
local rAlign   = Row("Curve Align")
local rAbility = Row("Ability")
local rFires   = Row("Fires / Status")
local cA, cABg, cT, cTBg, cS, cSBg = ChipRow()

local hint = Instance.new("TextLabel", Body)
hint.Size = UDim2.new(1, 0, 0, 8); hint.BackgroundTransparency = 1
hint.Text = "LCtrl hide  ·  E manual parry"
hint.TextColor3 = T2; hint.Font = Enum.Font.Gotham
hint.TextSize = 6; hint.LayoutOrder = LO()
hint.TextXAlignment = Enum.TextXAlignment.Center

-- ================================================================
-- HUD LOOP
-- ================================================================
_connections[#_connections+1] = RunService.Heartbeat:Connect(function()
    UpdatePing()
    PollOutcome()

    local now2  = tick()
    local char2 = Player.Character
    local hrp2  = char2 and char2:FindFirstChild("HumanoidRootPart")

    if hrp2 and myAbilityBehav == AB.TELEPORT then
        local delta = (hrp2.Position - lastHRPPos).Magnitude
        if delta > 15 then teleportSkipUntil = now2 + TELEPORT_SKIP end
        lastHRPPos = hrp2.Position
    elseif hrp2 then
        lastHRPPos = hrp2.Position
    end

    if math.floor(now2 * 0.5) ~= math.floor((now2 - 0.016) * 0.5) then
        RefreshAbility(char2)
    end

    rDist.Text = dbSpeed > 0 and ("%.1f st"):format(dbDist) or "—"
    rDist.TextColor3 = dbDist < BASE_RADIUS * 1.5 and RD
                    or dbDist < 30               and YL or T0

    rSpeed.Text = dbSpeed > 0 and ("%.0f st/s"):format(dbSpeed) or "—"
    rSpeed.TextColor3 = dbSpeed > 200 and OR or T0

    if dbFrozen then
        rTTR.Text = "FROZEN ❄"; rTTR.TextColor3 = CY
    elseif dbTTR < 90 then
        rTTR.Text = ("%.3f s"):format(dbTTR)
        rTTR.TextColor3 = dbTTR <= dbFW and RD or T1
    else
        rTTR.Text = "—"; rTTR.TextColor3 = T2
    end

    rFW.Text       = ("%.1f ms"):format(dbFW * 1000)
    rFW.TextColor3 = dbFW > BASE_WINDOW * 1.3 and OR or TL

    rAdapt.Text       = ("%.1f ms"):format(liveWindow * 1000)
    rAdapt.TextColor3 = liveWindow > BASE_WINDOW and OR or TL

    -- Show display ping / stable timing ping so spikes are visible in HUD
    rPing.Text       = ("%.0f / %.0f ms"):format(smoothPing * 1000, stablePing * 1000)
    rPing.TextColor3 = smoothPing > 0.12 and RD or smoothPing > 0.06 and YL or GN

    rAlign.Text = ("%.0f%%"):format(dbAlign * 100)
    rAlign.TextColor3 = dbCurveGated and RD
                     or dbAlign > 0.7 and GN
                     or dbAlign > 0.45 and YL or OR

    local suppRemaining = math.max(0, suppressUntil - tick())
    local abilityDisplay = dbAbility ~= "—" and dbAbility:sub(1, 14) or "—"
    if suppRemaining > 0.05 then
        abilityDisplay = abilityDisplay .. (" (%.1fs)"):format(suppRemaining)
    elseif dbAbilityTag ~= "" then
        abilityDisplay = abilityDisplay .. " " .. dbAbilityTag
    end
    rAbility.Text = abilityDisplay
    rAbility.TextColor3 = abilityGated and RD
                       or myAbilityBehav == AB.PULL and GN
                       or myAbilityBehav ~= AB.NONE and YL or T2

    rFires.Text       = ("%d  %s"):format(fireCount, dbStatus)
    rFires.TextColor3 = dbStatus == "HIT✓" and GN
                     or dbStatus == "MISS↑" and RD or T1

    cA.Text = autoOn and "AUTO ON" or "OFF"
    cABg.BackgroundColor3 = autoOn and AC or S2
    cA.TextColor3 = autoOn and T0 or T2

    cT.Text = dbTarget and "TARGET" or "SAFE"
    cTBg.BackgroundColor3 = dbTarget and RD or S2
    cT.TextColor3 = dbTarget and T0 or T2

    local firing = dbTarget and (dbTTR <= dbFW or dbFrozen or dbDist <= BASE_RADIUS * EMERG_MULT)
    cS.Text = firing and "◆ FIRE" or "ARMED"
    cSBg.BackgroundColor3 = firing and RD or S2
    cS.TextColor3 = firing and T0 or T2
end)

print("[LH13.2-delayed] loaded — delay=" .. (FIRE_DELAY_OFFSET*1000) .. "ms  LCtrl=hide  E=manual")