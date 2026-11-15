-- Prove2me | solution 1 for PagingDelay.PMD.proposition_17
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-14T08:45:46.903149+00:00
-- url     : https://prove2.me/submissions/889342e6-49bd-4e02-8c33-b2342a21fd8b

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Definitions.Def_PagingDelay_PMD_Path

/-! ## Inlined from `PagingWithDelay.Imports` -/
section

/-!
# The parts of Mathlib that the formalization uses

Instead of all of Mathlib, `Model.lean` and `BBN.lean` import these modules: they contain every Mathlib declaration the formalization uses, and only about a quarter of Mathlib, which keeps compilation lighter.
-/
end

/-! ## Inlined from `PagingWithDelay.Model` -/
section

/-!
# Weighted paging with delay

Every definition that the main theorem mentions (the section "Problem definition" of the paper): requests and instances, schedules and their cost, and randomized algorithms.

There are `n` pages (a `Fintype`), page `i` has weight `wᵢ > 0`, and the cache holds `k` pages, `0 < k < n`. A request `(p, a, d)` asks for page `p`; it is revealed at its arrival time `a` together with its delay cost function `d`, and if it is served at time `τ ≥ a`, it costs `d (τ - a)`. Delay cost functions are nondecreasing, continuous and unbounded with `d 0 = 0`. The paper's delay cost functions are defined on `[0, ∞)`; here they are defined on `ℝ` (extend by `0` to negative arguments, which keeps them monotone and continuous), and only nonnegative arguments are ever used. Arrival times may be negative, which does not matter.
-/

namespace PagingWithDelay

/-- A request for `page`, revealed at `arrival` together with its delay cost function `delay`: served at time `τ ≥ arrival`, it costs `delay (τ - arrival)`. -/
structure Request (Page : Type*) where
  page : Page
  arrival : ℝ
  delay : ℝ → ℝ
  delay_mono : Monotone delay
  delay_continuous : Continuous delay
  delay_zero : delay 0 = 0
  delay_unbounded : ∀ M : ℝ, ∃ τ, M ≤ delay τ

/-- An instance: positive page weights, a cache size `0 < k < n`, the initial cache `C₀` of `k` pages and a finite list of requests. The order of the list only breaks ties between simultaneous choices. -/
structure Instance (Page : Type*) [Fintype Page] where
  weight : Page → ℝ
  weight_pos : ∀ p, 0 < weight p
  cacheSize : ℕ
  cacheSize_pos : 0 < cacheSize
  cacheSize_lt : cacheSize < Fintype.card Page
  initialCache : Finset Page
  initialCache_card : initialCache.card = cacheSize
  requests : List (Request Page)

namespace Instance

variable {Page : Type*} [Fintype Page]

/-- The total weight `∑ᵢ wᵢ` of all pages. -/
noncomputable def totalWeight (input : Instance Page) : ℝ :=
  ∑ p, input.weight p

/-- The instance as known at time `t`: the requests that have arrived by `t` (with their delay functions); weights, cache size and initial cache are known from the start. -/
noncomputable def upTo (input : Instance Page) (t : ℝ) : Instance Page :=
  { input with requests := input.requests.filter fun ρ => decide (ρ.arrival ≤ t) }

end Instance

/-! ## Schedules -/

/-- A step of a schedule: at `time`, the cache is replaced by `cache`. -/
structure Step (Page : Type*) where
  time : ℝ
  cache : Finset Page

/-- A schedule: a finite list of steps, starting from the initial cache. Several steps may have the same time: the schedule then goes through several caches at one instant, ending with the cache of the last of these steps. -/
abbrev Schedule (Page : Type*) := List (Step Page)

namespace Schedule

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The fetch cost of `S` starting from the cache `C`: every step pays the weights of the pages it adds to the cache. -/
noncomputable def costFrom (weight : Page → ℝ) : Finset Page → Schedule Page → ℝ
  | _, [] => 0
  | C, step :: rest => (∑ p ∈ step.cache \ C, weight p) + costFrom weight step.cache rest

/-- The fetch cost of `S`, starting from the initial cache. -/
noncomputable def fetchCost (input : Instance Page) (S : Schedule Page) : ℝ :=
  costFrom input.weight input.initialCache S

/-- Page `p` is cached by `S` at time `s`: it is in one of the caches that `S` goes through at time `s`. The initial cache is present until the time of the first step, and the cache of step `j` from its time to the time of step `j + 1` (forever, if `j` is the last step). -/
def CachedAt (input : Instance Page) (S : Schedule Page) (p : Page) (s : ℝ) : Prop :=
  (p ∈ input.initialCache ∧ ∀ step ∈ S.head?, s ≤ step.time) ∨
    ∃ (j : ℕ) (h : j < S.length), S[j].time ≤ s ∧
      (∀ step ∈ S[j + 1]?, s ≤ step.time) ∧ p ∈ S[j].cache

/-- A feasible schedule: steps in chronological order, at most `k` pages cached, and every request served, i.e., its page is cached at some time after its arrival. -/
structure Feasible (input : Instance Page) (S : Schedule Page) : Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  capacity : ∀ step ∈ S, step.cache.card ≤ input.cacheSize
  serves : ∀ ρ ∈ input.requests, ∃ s, ρ.arrival ≤ s ∧ CachedAt input S ρ.page s

/-- The time at which `S` serves the request `ρ`: the first time `τ ≥ a_ρ` at which its page is cached. -/
noncomputable def serviceTime (input : Instance Page) (S : Schedule Page) (ρ : Request Page) : ℝ :=
  sInf {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ}

/-- The cost of `S`: its fetch cost plus the delay cost `∑_ρ d_ρ(τ_ρ - a_ρ)`. -/
noncomputable def cost (input : Instance Page) (S : Schedule Page) : ℝ :=
  fetchCost input S +
    (input.requests.map fun ρ => ρ.delay (serviceTime input S ρ - ρ.arrival)).sum

/-- The steps up to time `t`. -/
noncomputable def upTo (S : Schedule Page) (t : ℝ) : Schedule Page :=
  S.filter fun step => decide (step.time ≤ t)

end Schedule

/-! ## Randomized algorithms

A randomized algorithm turns every instance into a probability distribution on schedules. It is *online* if the distribution of its steps up to any time `t` depends only on the requests revealed by time `t`; then its steps up to `t` can be drawn at time `t`, conditionally on the steps drawn before. Since the delay functions are revealed on arrival, online algorithms are clairvoyant. -/

/-- A randomized algorithm: a distribution on schedules for every instance. -/
abbrev RandAlgorithm (Page : Type*) [Fintype Page] := Instance Page → PMF (Schedule Page)

namespace RandAlgorithm

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- **Online**: the distribution of the steps up to time `t` depends only on the requests revealed by time `t`. -/
def Online (alg : RandAlgorithm Page) : Prop :=
  ∀ (first second : Instance Page) (t : ℝ), first.upTo t = second.upTo t →
    (alg first).map (Schedule.upTo · t) = (alg second).map (Schedule.upTo · t)

/-- **Feasible**: with probability `1`, the schedule is feasible (so every request is served). -/
def Feasible (alg : RandAlgorithm Page) : Prop :=
  ∀ (input : Instance Page), ∀ S ∈ (alg input).support, S.Feasible input

/-- The expected cost `E[cost(S)]` of the random schedule `S`. -/
noncomputable def expectedCost (alg : RandAlgorithm Page) (input : Instance Page) : ENNReal :=
  ∑' S, alg input S * ENNReal.ofReal (S.cost input)

end RandAlgorithm

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Notation` -/
section

/-!
# Notation of the paper

`open scoped PagingWithDelay.InstanceNotation` lets a section write the parameters of the instance named `input` as in the paper: `w i` for the weight `wᵢ`, `k` for the cache size, `δ` and `L`. The notation is unhygienic: it refers to whatever variable is called `input` at the use site. While it is open, `w`, `k`, `δ` and `L` cannot be variable names.
-/

namespace PagingWithDelay

/-- `L = ln (2k+1)`, the logarithm of the paper (`L ≤ ln k + 1.1`, `Instance.L_le_log_add`). -/
noncomputable def Instance.L {Page : Type*} [Fintype Page] (input : Instance Page) : ℝ :=
  Real.log (2 * input.cacheSize + 1)

/-- The threshold `δ = 1/(2k+1)`: a page with missing mass `δ` counts as cached. -/
noncomputable def Instance.delta {Page : Type*} [Fintype Page] (input : Instance Page) : ℝ :=
  1 / (2 * input.cacheSize + 1)

namespace InstanceNotation

set_option hygiene false

/-- The weight `wᵢ` of page `i`. -/
scoped notation "w" => input.weight
/-- The cache size `k`. -/
scoped notation "k" => input.cacheSize
/-- The threshold `δ = 1/(2k+1)`. -/
scoped notation "δ" => input.delta
/-- The logarithm `L = ln (2k+1)`. -/
scoped notation "L" => input.L

end InstanceNotation

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Fractional` -/
section

/-!
# The fractional relaxation

Fractional schedules, their fetch cost (`def:fracfetch`) and delay cost (`def:fracdelay`), and deterministic fractional algorithms. `PMD` is such an algorithm; these definitions belong to the proof, not to the statement of the main theorem.

A fractional state `x : Page → ℝ` gives the *missing mass* of every page: `1 - xᵢ` of page `i` is cached. States lie in `[δ, 1]ⁿ` with total missing mass at least `n - k` (cached mass at most `k`), and a page with `xᵢ = δ` counts as cached.

A fractional schedule is a finite list of waypoints `(time, state)`, traversed in order (`x⁽⁰⁾, …, x⁽ᴺ⁾` in `sec:length`). The state is constant between consecutive waypoint times; waypoints with the same time are traversed at one instant. The requests arriving at time `t` arrive before the waypoints with time `t`.
-/

namespace PagingWithDelay

/-- A waypoint: the fractional schedule is in state `state` at `time`. -/
structure Waypoint (Page : Type*) where
  time : ℝ
  state : Page → ℝ

/-- A fractional schedule: a list of waypoints. -/
abbrev FracSchedule (Page : Type*) := List (Waypoint Page)

namespace FracSchedule

variable {Page : Type*} [Fintype Page]

open scoped InstanceNotation in
/-- The fractional fetch cost `∑ᵥ ∑ᵢ wᵢ (x⁽ᵛ⁾ᵢ - x⁽ᵛ⁺¹⁾ᵢ)⁺` (`def:fracfetch`). -/
noncomputable def fetchCost (input : Instance Page) : FracSchedule Page → ℝ
  | a :: b :: rest =>
      (∑ i, w i * max 0 (a.state i - b.state i)) + fetchCost input (b :: rest)
  | _ => 0

/-- The state right before time `t`: the state of the last waypoint with time `< t`, or of the first waypoint if there is none. -/
noncomputable def stateBefore (X : FracSchedule Page) (t : ℝ) : Page → ℝ :=
  match (X.filter fun w => decide (w.time < t)).getLast? with
  | some w => w.state
  | none => (X.head?.map Waypoint.state).getD fun _ => 1

/-- The time `τ_ρ` at which `ρ` is served: the first time `≥ a_ρ` of a waypoint at which its page has missing mass `δ`. -/
noncomputable def serviceTime (input : Instance Page) (X : FracSchedule Page)
    (ρ : Request Page) : ℝ :=
  sInf {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧ w.time = s}

open scoped InstanceNotation in
/-- The fractional delay cost `∑_ρ α_ρ d_ρ(τ_ρ - a_ρ)` (`def:fracdelay`), where `α_ρ = x_p - δ` for the state `x` right before the arrival of `ρ`. -/
noncomputable def delayCost (input : Instance Page) (X : FracSchedule Page) : ℝ :=
  (input.requests.map fun ρ =>
    (stateBefore X ρ.arrival ρ.page - δ) *
      ρ.delay (serviceTime input X ρ - ρ.arrival)).sum

/-- The cost of a fractional schedule: fractional fetch cost plus fractional delay cost. -/
noncomputable def cost (input : Instance Page) (X : FracSchedule Page) : ℝ :=
  fetchCost input X + delayCost input X

/-- A feasible fractional schedule: chronological waypoints whose states lie in `[δ, 1]ⁿ` with total missing mass at least `n - k`, and every request served at a waypoint at or after its arrival. -/
structure Feasible (input : Instance Page) (X : FracSchedule Page) : Prop where
  chronological : X.Pairwise fun earlier later => earlier.time ≤ later.time
  bounds : ∀ w ∈ X, ∀ i, input.delta ≤ w.state i ∧ w.state i ≤ 1
  mass : ∀ w ∈ X, (Fintype.card Page : ℝ) - input.cacheSize ≤ ∑ i, w.state i
  serves : ∀ ρ ∈ input.requests, ∃ w ∈ X,
    ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta

/-- The waypoints up to time `t`. -/
noncomputable def upTo (X : FracSchedule Page) (t : ℝ) : FracSchedule Page :=
  X.filter fun w => decide (w.time ≤ t)

end FracSchedule

/-- A deterministic fractional algorithm: a fractional schedule for every instance. -/
abbrev FracAlgorithm (Page : Type*) [Fintype Page] := Instance Page → FracSchedule Page

namespace FracAlgorithm

variable {Page : Type*} [Fintype Page]

/-- **Online**: the waypoints up to time `t` depend only on the requests revealed by time `t`. -/
def Online (alg : FracAlgorithm Page) : Prop :=
  ∀ (first second : Instance Page) (t : ℝ), first.upTo t = second.upTo t →
    (alg first).upTo t = (alg second).upTo t

/-- **Feasible**: every instance receives a feasible fractional schedule. -/
def Feasible (alg : FracAlgorithm Page) : Prop :=
  ∀ input : Instance Page, (alg input).Feasible input

end FracAlgorithm

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Algorithm` -/
section

/-!
# The algorithm `PMD` (preemptive mirror descent)

Section 3 (`sec:alg`) of `paper/paper.tex` (pseudocode `PreemptiveMirrorDescent`) as an event loop. It keeps the fractional state `x` (missing masses), a budget `B_W` per level `W`, the pending requests, and the claimed delay `c_q` of every page (`claims`).

Notation, for the current pending requests and a time `t`:
* `delay_q(t) = ∑_{ρ pending on q} d_ρ(t - a_ρ)` (`pageDelay`);
* the overshoot `o_q(t) = (delay_q(t) - c_q - w_q)⁺` (`overshoot`);
* `eq:trigger` holds for page `p` at `t` (`TriggerCond`) if `o_p(t) > 0` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_{x→p}| / L`;
* page `p` *becomes critical* at `t` (`Critical`) if `t` is the last moment before `eq:trigger` holds: it holds at times `τ ≥ t` arbitrarily close to `t`;
* the critical service on `p` from `x` follows the mirror descent path `λ(s)ᵢ = min 1 (xᵢ e^{s/wᵢ})` (`i ≠ p`), `λ(s)_p = n - k - ∑_{i ≠ p} λ(s)ᵢ` (`mdPath`), up to its length `|λ| = min {s ≥ 0 : λ(s)_p = δ}` (`serviceEnd`).

The loop, in the idle stage at time `now`:
1. If some page is critical at `now`, the first such page `p` (in the fixed order `Finset.univ.toList`) gets a **critical service** `λ`: every page `q` with `w_q ≤ w_p` raises `c_q` by the same fraction `θ` of its overshoot, `|λ| / L` in total; `x ← λ(|λ|)`; all pending requests on `p` are served and `c_p ← 0`; and `|λ|_W = |I_W ∩ [0, |λ|]|` with `I_W = [L W, 2 L W)` is deposited into `B_W` for every level `W ≥ w_p`. Then the levels `W = w_min, 2 w_min, …, w_max` are examined in increasing order; a **level-`W` preemptive service** runs if `B_W ≥ 4W` and the pages of weight `≤ W` hold cached mass at least `1 - δ`: it opens a hole (every page of weight `≤ W` gives up the same fraction of its cached mass, `1 - δ` in total) and pays `W (1 - δ)` from `B_W`; while `B_W ≥ W`, it performs a round trip (`x_q ← δ`, then back) on the pending page `q` of weight `≤ W` with the earliest deadline `inf {τ ≥ t : delay_q(τ) > w_q}`, serving all pending requests on `q`, resetting `c_q` and paying `w_q (x_q - δ)`; finally it closes the hole.
2. Otherwise the loop advances to the infimum of the times `≥ now` at which `eq:trigger` holds for some page (some page is critical there, and it is later than `now`), unless the next arrival comes no later; then it advances to that arrival time, where its requests arrive. A request on a page with `x_p = δ` is served on arrival.

The loop is a deterministic state machine `next`. Every move records the waypoints of the fractional schedule (`waypoints`): the state after a critical service, after opening a hole, at the bottom of a round trip and after it, and after closing the hole (the states `x⁽ᵛ⁾` of `sec:length`). Ticks and advances record the unchanged state at their time.

**Differences from the paper.**
* *Ties* (several pages critical at once, equal deadlines) are broken by a fixed order of the pages and by the order of the pending requests.
* *Levels* are indexed by exponents: page `p` has level `⌈log₂ w_p⌉` (`log₂ w_p` for power-of-two weights), and `B_W` for `W = 2^e` is `budget e`. Only the levels `w_min ≤ W ≤ w_max` are examined and receive deposits. This is no restriction: no level `W < w_min` receives a deposit, and no level `W ≥ w_max` does either, since at `s = L w_max` every page `i ≠ p` has `λ(s)ᵢ = 1` (`eq:light_evicted_in_band`), so `|λ| ≤ L w_max`.
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

noncomputable section

variable (input : Instance Page)

/-! ### Levels -/

/-- The level `⌈log₂ w⌉` of a page. -/
def level (p : Page) : ℤ := Int.clog 2 (w p)

/-- The lightest level `log₂ w_min`. -/
def minLevel : ℤ := ⨅ p, level input p

/-- The heaviest level `log₂ w_max`. -/
def maxLevel : ℤ := ⨆ p, level input p

/-- The weight `W = 2^e` of level `e`. -/
def levelWeight (e : ℤ) : ℝ := (2 : ℝ) ^ e

/-- The total missing mass `n - k` of a full cache. -/
def restMass : ℝ := (Fintype.card Page : ℝ) - k

/-! ### The critical service -/

/-- The missing mass `x_i(s) = min 1 (x_i e^{s/w_i})` of a page `i ≠ p` at time `s` of the mirror descent path from `x`. -/
def evictCurve (x : Page → ℝ) (i : Page) (s : ℝ) : ℝ :=
  min 1 (x i * Real.exp (s / w i))

/-- The mirror descent path `x(s)` of a critical service on `p` from `x`: the pages `i ≠ p` grow exponentially at rate `1/w_i` up to `1`, and `x_p(s) = n - k - ∑_{i ≠ p} x_i(s)`. -/
def mdPath (x : Page → ℝ) (p : Page) (s : ℝ) : Page → ℝ := fun i =>
  if i = p then restMass input - ∑ j ∈ Finset.univ.erase p, evictCurve input x j s
  else evictCurve input x i s

/-- The end `s^end` of the critical service: the least `s` with `x_p(s) ≤ δ` (equivalently `x_p(s) = δ`, as `x_p(s)` is continuous). -/
def serviceEnd (x : Page → ℝ) (p : Page) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ mdPath input x p s p ≤ δ}

/-- The state `x(s^end)` at the end of the critical service on `p`. -/
def criticalState (x : Page → ℝ) (p : Page) : Page → ℝ :=
  mdPath input x p (serviceEnd input x p)

/-! ### The preemptive service -/

/-- The fraction `θ` by which a level-`W` preemptive service raises the pages of weight `≤ W` when it opens its hole: `θ ∑_{i : w_i ≤ W} (1 - x_i) = 1 - δ`. Capped at `1`, which matters only if these pages hold less than `1 - δ` cached mass, when no hole is opened. -/
def holeFraction (x : Page → ℝ) (e : ℤ) : ℝ :=
  min 1 ((1 - δ) /
    ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i))

/-- The state of a level-`W` preemptive service after it opens its hole: every page `i` of weight `≤ W` gives up the same fraction `θ` (`holeFraction`) of its cached mass, `x_i ← x_i + θ (1 - x_i)`. -/
def hole (x : Page → ℝ) (e : ℤ) : Page → ℝ := fun i =>
  if level input i ≤ e then x i + holeFraction input x e * (1 - x i) else x i

/-- The payment `B_W ← B_W - W (1 - δ)` of a level-`W` preemptive service for creating its hole; it covers refetching the light pages when the hole is closed. -/
def holePayment (e : ℤ) : ℝ := levelWeight e * (1 - δ)

/-- The condition for a level-`W` preemptive service: `B_W ≥ 4W`, and the pages of weight `≤ W` hold cached mass `∑_{i : w_i ≤ W} (1 - x_i) ≥ 1 - δ`. -/
def preemptCondition (x : Page → ℝ) (budget : ℤ → ℝ) (e : ℤ) : Prop :=
  4 * levelWeight e ≤ budget e ∧
    1 - δ ≤ ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)

/-- The cost `w_q (x_q - δ)` of a round trip on `q` from the current state `x` (inside the hole): decrease `x_q` to `δ` and back. -/
def tripCost (x : Page → ℝ) (p : Page) : ℝ :=
  w p * (x p - δ)

/-! ### Initial state and stages -/

/-- Where the event loop is: waiting for the next trigger or arrival (`idle`), about to examine level `e` in the level loop following a critical service (`examine e`), or inside a level-`e` preemptive service whose hole was created from the state `base` (`preempt e base`). -/
inductive Stage (Page : Type*) where
  | idle
  | examine (e : ℤ)
  | preempt (e : ℤ) (base : Page → ℝ)

/-- The page outside `C₀` that holds missing mass `1 - kδ` in the initial state: the first page outside `C₀` in the fixed order `Finset.univ.toList`. -/
def initialPage : Option Page :=
  Finset.univ.toList.find? fun i => decide (i ∉ input.initialCache)

/-- The initial state (Appendix A): missing mass `δ` on the pages of `C₀`, `1 - kδ` on one page outside `C₀` (`initialPage`) and `1` on the others, total `n - k`. -/
def initialState (i : Page) : ℝ :=
  if i ∈ input.initialCache then δ
  else if initialPage input = some i then 1 - k * δ
  else 1

/-- The stage after level `e` has been dealt with. -/
def afterLevel (e : ℤ) : Stage Page :=
  if e < maxLevel input then .examine (e + 1) else .idle

/-! ### Delays, overshoots and the trigger -/

/-- `delay_p(t)`: the total delay at time `t` of the pending requests on `p`. -/
def pageDelay (pending : List (Request Page)) (p : Page) (t : ℝ) : ℝ :=
  ((pending.filter fun ρ => decide (ρ.page = p)).map fun ρ => ρ.delay (t - ρ.arrival)).sum

/-- The overshoot `o_p(t) = (delay_p(t) - c_p - w_p)⁺`. -/
def overshoot (pending : List (Request Page)) (claims : Page → ℝ) (p : Page) (t : ℝ) : ℝ :=
  max 0 (pageDelay pending p t - claims p - w p)

/-- The pages `q` with `w_q ≤ w_p`. -/
def lighter (p : Page) : Finset Page :=
  Finset.univ.filter fun q => w q ≤ w p

/-- The trigger condition `eq:trigger` for page `p` at time `t` in the state `x`: `o_p(t) > 0` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L`. -/
def TriggerCond (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  0 < overshoot input pending claims p t ∧
    serviceEnd input x p / L ≤
      ∑ q ∈ lighter input p, overshoot input pending claims q t

/-- Page `p` becomes critical at time `t`: `t` is the last moment before `eq:trigger` holds, i.e. `eq:trigger` holds at times `τ ≥ t` arbitrarily close to `t`. -/
def Critical (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  ∀ ε > 0, ∃ τ, t ≤ τ ∧ τ < t + ε ∧ TriggerCond input x pending claims τ p

/-- The fraction `θ` of the overshoots claimed by a critical service on `p` at time `t` from the state `x`: `θ ∑_{q : w_q ≤ w_p} o_q(t) = |λ_p(x)| / L`. Capped at `1`, which matters only if `p` is not critical at `t` (otherwise `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L` by continuity). -/
def claimFraction (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : ℝ :=
  min 1 (serviceEnd input x p / L /
    ∑ q ∈ lighter input p, overshoot input pending claims q t)

/-- The claims of a critical service on `p` at time `t` from the state `x`: every page `q` with `w_q ≤ w_p` claims the same fraction `θ` of its overshoot, `c_q ← c_q + θ o_q(t)`, so that `|λ_p(x)| / L` is claimed in total. -/
def claimUpdate (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Page → ℝ := fun q =>
  if q ∈ lighter input p then
    claims q + claimFraction input x pending claims t p * overshoot input pending claims q t
  else claims q

/-! ### Deposits -/

/-- The length `|λ|_W = |I_W ∩ [0, |λ|]|` of the part of the critical service on `p` from `x` in `I_W = [L W, 2 L W)`, for the level `e`, `W = 2^e`. -/
def levelLen (x : Page → ℝ) (p : Page) (e : ℤ) : ℝ :=
  min (2 * L * levelWeight e) (serviceEnd input x p) -
    min (L * levelWeight e) (serviceEnd input x p)

/-- The deposits of a critical service `λ` on `p` from `x`: `B_W ← B_W + |λ|_W` for every level `W` with `w_p ≤ W ≤ w_max`. -/
def deposit (x : Page → ℝ) (p : Page) (budget : ℤ → ℝ) : ℤ → ℝ := fun e =>
  if level input p ≤ e ∧ e ≤ maxLevel input then budget e + levelLen input x p e
  else budget e

/-! ### Round trips -/

/-- The deadline `inf {τ ≥ t : delay_p(τ) > w_p}` of the pending requests on `p` at time `t`. -/
def pageDeadline (pending : List (Request Page)) (t : ℝ) (p : Page) : ℝ :=
  sInf {τ | t ≤ τ ∧ w p < pageDelay pending p τ}

/-- The next round trip of a level-`W` preemptive service at time `t`: the pending request on a page of weight `≤ W` whose page has the earliest deadline (the first such in the pending list). -/
def tripCandidate (pending : List (Request Page)) (t : ℝ) (e : ℤ) : Option (Request Page) :=
  (pending.filter fun ρ => decide (level input ρ.page ≤ e)).argmin
    fun ρ => pageDeadline input pending t ρ.page

/-! ### The event loop -/

/-- The loop state: the current time `now`, the arrival times `upcoming` still to be processed, the fractional state `x` (inside a preemptive service, the state with the hole), the budget `budget e` (`B_W`) of level `e`, the `pending` requests, the used amount `claims q` (`c_q`) of the delay of page `q`, and the `stage` (see `Stage`). -/
structure Snap (Page : Type*) where
  now : ℝ
  upcoming : List ℝ
  x : Page → ℝ
  budget : ℤ → ℝ
  pending : List (Request Page)
  claims : Page → ℝ
  stage : Stage Page

/-- One move of the loop. -/
inductive Move (Page : Type*) where
  /-- Arrivals at time `t`. -/
  | tick (t : ℝ)
  /-- Advance to the time `t` at which some page becomes critical first. -/
  | advance (t : ℝ)
  /-- A critical service on page `p`. -/
  | critical (p : Page)
  /-- Level `e` examined; the condition for its preemptive service fails. -/
  | skip (e : ℤ)
  /-- Level `e` examined; its preemptive service creates the hole and pays `W (1 - δ)`. -/
  | openHole (e : ℤ)
  /-- A round trip on `π.page`, selected by the pending request `π`. -/
  | trip (e : ℤ) (π : Request Page)
  /-- The level-`e` preemptive service closes its hole: no candidate is left (`none`), or the budget is too small for the next round trip, `B_W < W` (`some π`, the candidate that is not served). -/
  | closeHole (e : ℤ) (stop : Option (Request Page))

/-- The distinct arrival times, in increasing order. -/
def arrivalTimes : List ℝ :=
  (input.requests.map Request.arrival).toFinset.sort (· ≤ ·)

/-- The loop state before the first move; `now` is the first arrival time, so times never decrease along the run. -/
def initialSnap : Snap Page where
  now := (arrivalTimes input).headD 0
  upcoming := arrivalTimes input
  x := initialState input
  budget := fun _ => 0
  pending := []
  claims := fun _ => 0
  stage := .idle

/-- The page served by the next critical service at time `s.now`: the first page (in the fixed order `Finset.univ.toList`) that is critical at `s.now`. -/
def triggerPage (s : Snap Page) : Option Page :=
  (Finset.univ.toList).find? fun p => decide (Critical input s.x s.pending s.claims s.now p)

/-- The times `≥ now` at which `eq:trigger` holds for some page, for the current state, pending requests and claims. -/
def triggerTimes (s : Snap Page) : Set ℝ :=
  {t | s.now ≤ t ∧ ∃ p, TriggerCond input s.x s.pending s.claims t p}

/-- One move of `PMD`, or `none` when the run is over. -/
def next (s : Snap Page) : Option (Move Page × Snap Page) :=
  match s.stage with
  | .idle =>
      match triggerPage input s with
      | some p =>
          some (.critical p,
            { s with
              x := criticalState input s.x p
              budget := deposit input s.x p s.budget
              pending := s.pending.filter fun π => decide (π.page ≠ p)
              claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
              stage := .examine (minLevel input) })
      | none =>
          if (triggerTimes input s).Nonempty ∧
              ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a then
            some (.advance (sInf (triggerTimes input s)),
              { s with now := sInf (triggerTimes input s) })
          else
            match s.upcoming with
            | [] => none
            | t :: rest =>
                some (.tick t,
                  { s with
                    now := t
                    upcoming := rest
                    pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
                      fun ρ => decide (s.x ρ.page ≠ δ) })
  | .examine e =>
      if preemptCondition input s.x s.budget e then
        some (.openHole e,
          { s with
            x := hole input s.x e
            budget := Function.update s.budget e (s.budget e - holePayment input e)
            stage := .preempt e s.x })
      else
        some (.skip e, { s with stage := afterLevel input e })
  | .preempt e base =>
      match tripCandidate input s.pending s.now e with
      | none => some (.closeHole e none, { s with x := base, stage := afterLevel input e })
      | some π =>
          if levelWeight e ≤ s.budget e then
            some (.trip e π,
              { s with
                budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
                pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
                claims := Function.update s.claims π.page 0 })
          else
            some (.closeHole e (some π), { s with x := base, stage := afterLevel input e })

/-- The waypoints a move records, given the state before it. -/
def waypoints (pre : Snap Page) : Move Page → List (Waypoint Page)
  | .tick t => [⟨t, pre.x⟩]
  | .advance t => [⟨t, pre.x⟩]
  | .critical p => [⟨pre.now, criticalState input pre.x p⟩]
  | .skip _ => []
  | .openHole e => [⟨pre.now, hole input pre.x e⟩]
  | .trip _ π => [⟨pre.now, Function.update pre.x π.page δ⟩, ⟨pre.now, pre.x⟩]
  | .closeHole _ _ =>
      match pre.stage with
      | .preempt _ base => [⟨pre.now, base⟩]
      | _ => []

/-- A log entry: the state before a move and the move. -/
abbrev Entry (Page : Type*) := Snap Page × Move Page

/-- Run at most `fuel` moves from `s`; returns the log and the final state. -/
def run : ℕ → Snap Page → List (Entry Page) × Snap Page
  | 0, s => ([], s)
  | fuel + 1, s =>
      match next input s with
      | none => ([], s)
      | some (m, s') =>
          let rest := run fuel s'
          ((s, m) :: rest.1, rest.2)

/-- The number of levels `log₂ w_max - log₂ w_min + 1`. -/
def numLevels : ℕ := (maxLevel input - minLevel input + 1).toNat

/-- A bound on the number of moves: every tick consumes an arrival time, every critical service and round trip serves a request, every advance is followed by a critical service, and between two critical services at most two moves per level are made. -/
def fuel : ℕ :=
  (4 * input.requests.length + 1) * (2 * numLevels input + 4) + 1

/-- The log of `PMD` on `input`. -/
def log : List (Entry Page) := (run input (fuel input) (initialSnap input)).1

end

end PMD

/-- **The algorithm `PMD`** (`PreemptiveMirrorDescent`): the fractional schedule recorded by the event loop. -/
noncomputable def preemptiveMirrorDescent {Page : Type*} [Fintype Page] [DecidableEq Page] :
    FracAlgorithm Page :=
  fun input => (PMD.log input).flatMap fun entry => PMD.waypoints input entry.1 entry.2

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Basic` -/
section

/-!
# Basic facts: the standing assumptions, constants, levels, fractional states

`Instance.Valid` collects the assumptions that `Instance` and `Request` carry as fields (`Instance.valid`); the internal lemmas take it as a hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

namespace Instance

variable (input) in
/-- All weights are (integer) powers of two. -/
def PowerOfTwoWeights : Prop :=
  ∀ p, ∃ e : ℤ, w p = 2 ^ e

variable (input) in
/-- The standing assumptions on an instance: positive weights, `0 < k < n`, an initial cache of `k` pages, and delay cost functions that are nondecreasing, continuous and unbounded with `d 0 = 0`. -/
structure Valid : Prop where
  weight_pos : ∀ p, 0 < w p
  cacheSize_pos : 0 < k
  cacheSize_lt : k < Fintype.card Page
  initialCache_card : input.initialCache.card = k
  delay_mono : ∀ ρ ∈ input.requests, Monotone ρ.delay
  delay_continuous : ∀ ρ ∈ input.requests, Continuous ρ.delay
  delay_zero : ∀ ρ ∈ input.requests, ρ.delay 0 = 0
  delay_unbounded : ∀ ρ ∈ input.requests, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ

variable (input) in
/-- Every instance satisfies the standing assumptions. -/
theorem valid : input.Valid where
  weight_pos := input.weight_pos
  cacheSize_pos := input.cacheSize_pos
  cacheSize_lt := input.cacheSize_lt
  initialCache_card := input.initialCache_card
  delay_mono ρ _ := ρ.delay_mono
  delay_continuous ρ _ := ρ.delay_continuous
  delay_zero ρ _ := ρ.delay_zero
  delay_unbounded ρ _ := ρ.delay_unbounded

theorem delta_pos (hv : input.Valid) : 0 < δ := by
  unfold delta; positivity

theorem delta_lt_one (hv : input.Valid) : δ < 1 := by
  unfold delta
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_lt_one (by positivity)]; linarith

theorem L_pos (hv : input.Valid) : 0 < L := by
  unfold Instance.L
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  apply Real.log_pos; linarith

/-- `L = ln (2k+1) ≥ ln 3 ≥ 1`. -/
theorem one_le_L (hv : input.Valid) : 1 ≤ L := by
  unfold Instance.L
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have h3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- `δ ≤ 1/3`. -/
theorem delta_le_third (hv : input.Valid) : δ ≤ 1 / 3 := by
  unfold delta
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `L = ln (2k+1) ≤ ln (3k) = ln k + ln 3 < ln k + 1.1`. -/
theorem L_le_log_add (hv : input.Valid) : L ≤ Real.log k + 11 / 10 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have h3 : Real.log 3 < 11 / 10 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num),
      show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.exp_add]
    calc (3 : ℝ) < 2.7182818283 * (1 + 1 / 10 + (1 / 10) ^ 2 / 2) := by norm_num
      _ ≤ Real.exp 1 * Real.exp (1 / 10) :=
        mul_le_mul Real.exp_one_gt_d9.le (Real.quadratic_le_exp_of_nonneg (by norm_num))
          (by norm_num) (Real.exp_pos 1).le
  have h : Real.log (2 * k + 1) ≤ Real.log (3 * k) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  unfold Instance.L
  linarith

theorem totalWeight_nonneg (hv : input.Valid) : 0 ≤ input.totalWeight :=
  Finset.sum_nonneg fun p _ => (hv.weight_pos p).le

end Instance

namespace PMD


/-- A fractional state: all missing masses in `[δ, 1]`. -/
def IsFrac (input : Instance Page) (x : Page → ℝ) : Prop :=
  ∀ i, δ ≤ x i ∧ x i ≤ 1

/-- A rest state: a fractional state with total missing mass exactly `n - k`. -/
def IsRest (input : Instance Page) (x : Page → ℝ) : Prop :=
  IsFrac input x ∧ ∑ i, x i = restMass input

theorem delta_pos (hv : input.Valid) : 0 < δ := by
  unfold Instance.delta; positivity

theorem delta_lt_one (hv : input.Valid) : δ < 1 := by
  unfold Instance.delta
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_lt_one (by positivity)]; linarith

theorem L_pos (hv : input.Valid) : 0 < L := by
  unfold Instance.L
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  apply Real.log_pos; linarith

theorem log_delta (hv : input.Valid) : Real.log δ = -L := by
  unfold Instance.delta Instance.L
  rw [one_div, Real.log_inv]

theorem delta_mul_exp_L (hv : input.Valid) : δ * Real.exp L = 1 := by
  unfold Instance.delta Instance.L
  rw [Real.exp_log (by positivity)]
  field_simp

theorem levelWeight_pos (e : ℤ) : 0 < levelWeight e := by
  unfold levelWeight; positivity

theorem levelWeight_succ (e : ℤ) : levelWeight (e + 1) = 2 * levelWeight e := by
  unfold levelWeight
  rw [zpow_add₀ (by norm_num), zpow_one, mul_comm]

/-- A page has level `≤ e` iff its weight is at most `2^e`. -/
theorem level_le_iff (hv : input.Valid) (p : Page) (e : ℤ) :
    level input p ≤ e ↔ w p ≤ levelWeight e := by
  unfold level levelWeight
  have := Int.le_zpow_iff_clog_le (b := 2) (by norm_num) (x := e) (hv.weight_pos p)
  push_cast at this
  exact this.symm

theorem levelWeight_level (hv : input.Valid) (h2 : input.PowerOfTwoWeights) (p : Page) :
    levelWeight (level input p) = w p := by
  obtain ⟨e, he⟩ := h2 p
  unfold levelWeight level
  rw [he]
  have := Int.clog_zpow (R := ℝ) (b := 2) (by norm_num) e
  push_cast at this
  rw [this]

theorem minLevel_le (p : Page) : minLevel input ≤ level input p :=
  ciInf_le (Set.finite_range _).bddBelow p

theorem le_maxLevel (p : Page) : level input p ≤ maxLevel input :=
  le_ciSup (Set.finite_range _).bddAbove p

theorem card_pos (hv : input.Valid) : 0 < Fintype.card Page :=
  lt_of_le_of_lt (Nat.zero_le _) hv.cacheSize_lt

theorem nonempty_page (hv : input.Valid) : Nonempty Page :=
  Fintype.card_pos_iff.mp (card_pos hv)

theorem minLevel_le_maxLevel (hv : input.Valid) : minLevel input ≤ maxLevel input := by
  obtain ⟨p⟩ := nonempty_page hv
  exact (minLevel_le p).trans (le_maxLevel p)

/-- The initial page exists and lies outside `C₀`. -/
theorem initialPage_spec (hv : input.Valid) :
    ∃ p₀, initialPage input = some p₀ ∧ p₀ ∉ input.initialCache := by
  have hex : ∃ i, i ∉ input.initialCache := by
    by_contra h
    push_neg at h
    have : Finset.univ ⊆ input.initialCache := fun i _ => h i
    have := Finset.card_le_card this
    rw [Finset.card_univ, hv.initialCache_card] at this
    exact absurd hv.cacheSize_lt (not_lt.2 this)
  obtain ⟨i, hi⟩ := hex
  cases h : initialPage input with
  | none =>
      exfalso
      unfold initialPage at h
      have := List.find?_eq_none.1 h i (Finset.mem_toList.2 (Finset.mem_univ i))
      simp [hi] at this
  | some p₀ =>
      refine ⟨p₀, rfl, ?_⟩
      unfold initialPage at h
      simpa using List.find?_some h

theorem initialState_isRest (hv : input.Valid) : IsRest input (initialState input) := by
  obtain ⟨p₀, hp₀, hp₀C⟩ := initialPage_spec hv
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have hd := delta_pos hv
  have hd1 : δ * (2 * k + 1) = 1 := by
    unfold Instance.delta; field_simp
  have heq : initialState input = fun i =>
      (if i ∈ input.initialCache then δ else 1) -
        (if i = p₀ then k * δ else 0) := by
    funext i
    unfold initialState
    rw [hp₀]
    by_cases hi : i = p₀
    · subst hi; simp [hp₀C]
    · have : ¬ some p₀ = some i := fun h => hi (Option.some_injective _ h).symm
      split_ifs <;> simp_all
  refine ⟨fun i => ?_, ?_⟩
  · rw [heq]
    by_cases hi : i = p₀
    · subst hi; simp only [hp₀C, if_false, if_true]; constructor <;> nlinarith
    · simp only [hi, if_false, sub_zero]
      split_ifs
      · exact ⟨le_rfl, (delta_lt_one hv).le⟩
      · exact ⟨(delta_lt_one hv).le, le_rfl⟩
  · rw [heq, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ p₀, if_pos (Finset.mem_univ _)]
    have hc : (Finset.univ.filter (fun i => i ∈ input.initialCache)) = input.initialCache := by
      ext; simp
    have hc2 : (Finset.univ.filter (fun i => i ∉ input.initialCache)).card
        = Fintype.card Page - k := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hc,
        hv.initialCache_card, Finset.card_univ]
    rw [hc, hv.initialCache_card, hc2, nsmul_eq_mul, nsmul_eq_mul,
      Nat.cast_sub hv.cacheSize_lt.le]
    unfold restMass
    ring

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Critical.CurveAux` -/
section

/-!
# Helpers for the critical service curve
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- Telescoping over an integer interval. -/
theorem sum_Icc_telescope (g : ℤ → ℝ) (l : ℤ) :
    ∀ n : ℕ, ∑ e ∈ Finset.Icc l (l + n), (g (e + 1) - g e) = g (l + n + 1) - g l
  | 0 => by simp
  | n + 1 => by
    have hI : Finset.Icc l (l + ((n + 1 : ℕ) : ℤ)) = insert (l + n + 1) (Finset.Icc l (l + n)) := by
      ext e; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hn : (l + n + 1) ∉ Finset.Icc l (l + n) := by simp
    rw [hI, Finset.sum_insert hn, sum_Icc_telescope g l n]
    push_cast; ring_nf

theorem sum_Icc_telescope' (g : ℤ → ℝ) (l M : ℤ) (h : l ≤ M) :
    ∑ e ∈ Finset.Icc l M, (g (e + 1) - g e) = g (M + 1) - g l := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M = l + n := ⟨(M - l).toNat, by omega⟩
  subst hn
  exact sum_Icc_telescope g l n

theorem evictCurve_continuous (x : Page → ℝ) (i : Page) :
    Continuous (evictCurve input x i) :=
  continuous_const.min (continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const _)))

theorem evictCurve_mono (hv : input.Valid) {x : Page → ℝ} (i : Page) (hxi : 0 ≤ x i) :
    Monotone (evictCurve input x i) := by
  intro a b hab
  unfold evictCurve
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ hxi
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right hab (hv.weight_pos i).le

theorem evictCurve_zero {x : Page → ℝ} (i : Page) (hxi : x i ≤ 1) :
    evictCurve input x i 0 = x i := by
  unfold evictCurve
  simp [hxi]

theorem evictCurve_le_one (x : Page → ℝ) (i : Page) (s : ℝ) : evictCurve input x i s ≤ 1 :=
  min_le_left _ _

theorem mdPath_self (x : Page → ℝ) (r : Page) (s : ℝ) :
    mdPath input x r s r = restMass input - ∑ j ∈ Finset.univ.erase r, evictCurve input x j s := by
  simp [mdPath]

theorem mdPath_of_ne (x : Page → ℝ) (r : Page) (s : ℝ) {i : Page} (hi : i ≠ r) :
    mdPath input x r s i = evictCurve input x i s := by
  simp [mdPath, hi]

theorem mdPath_self_continuous (x : Page → ℝ) (r : Page) :
    Continuous fun s => mdPath input x r s r := by
  simp only [mdPath_self]
  exact continuous_const.sub (continuous_finset_sum _ fun j _ => evictCurve_continuous x j)

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Critical.Curve` -/
section

/-!
# The critical service (`sec:alg`)

Properties of the mirror descent path from a rest state `x` on a page `r` with `x r > δ`: it ends in a rest state with `x_r = δ`, the other pages only grow, and its length, fetch cost and interval evictions.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- The fetch `w_r (x_r - δ)` of the critical service on `r` from `x`. -/
noncomputable def criticalFetch (input : Instance Page) (x : Page → ℝ) (r : Page) : ℝ :=
  w r * (x r - δ)

/-- The weighted eviction `EV(φ) = ∑_{i ≠ r} wᵢ (xᵢ(s^end) - xᵢ)` of the critical service. -/
noncomputable def criticalEV (input : Instance Page) (x : Page → ℝ) (r : Page) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i * (criticalState input x r i - x i)

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
  (hr : δ < x r)
include hv hx hr

/-- The set whose infimum is the end of the critical service. -/
theorem serviceEnd_set_aux :
    (0 ≤ L * levelWeight (maxLevel input) ∧
      mdPath input x r (L * levelWeight (maxLevel input)) r ≤ δ) := by
  have hL := L_pos hv
  have hW := levelWeight_pos (maxLevel input)
  refine ⟨by positivity, ?_⟩
  rw [mdPath_self]
  have h1 : ∀ j ∈ Finset.univ.erase r,
      evictCurve input x j (L * levelWeight (maxLevel input)) = 1 := by
    intro j _
    unfold evictCurve
    apply min_eq_left
    have hwj := hv.weight_pos j
    have hle : w j ≤ levelWeight (maxLevel input) :=
      (level_le_iff hv j _).mp (le_maxLevel j)
    have hge : L ≤ L * levelWeight (maxLevel input) / w j := by
      rw [le_div_iff₀ hwj]
      exact mul_le_mul_of_nonneg_left hle hL.le
    calc (1 : ℝ) = δ * Real.exp L := (delta_mul_exp_L hv).symm
      _ ≤ x j * Real.exp (L * levelWeight (maxLevel input) / w j) := by
        apply mul_le_mul (hx.1 j).1 (Real.exp_le_exp.mpr hge) (Real.exp_pos _).le
        linarith [(hx.1 j).1, delta_pos hv]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ, nsmul_eq_mul, mul_one, restMass,
    Nat.cast_sub (card_pos hv)]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  push_cast
  linarith [delta_pos hv]

theorem serviceEnd_set_nonempty :
    {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ}.Nonempty :=
  ⟨_, serviceEnd_set_aux hv hx hr⟩

theorem serviceEnd_set_bdd :
    BddBelow {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ} :=
  ⟨0, fun s hs => hs.1⟩

theorem mdPath_zero : mdPath input x r 0 r = x r := by
  rw [mdPath_self, ← hx.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  rw [Finset.sum_congr rfl fun j _ => evictCurve_zero (input := input) j (hx.1 j).2]
  ring

theorem serviceEnd_nonneg : 0 ≤ serviceEnd input x r :=
  le_csInf (serviceEnd_set_nonempty hv hx hr) fun s hs => hs.1

/-- The critical service ends by path time `L · 2^{maxLevel}`, when all other pages are evicted. -/
theorem serviceEnd_le : serviceEnd input x r ≤ L * levelWeight (maxLevel input) :=
  csInf_le (serviceEnd_set_bdd hv hx hr) (serviceEnd_set_aux hv hx hr)

/-- Before its end, the critical service has `x_r(s) > δ`. -/
theorem delta_lt_mdPath {s : ℝ} (hs0 : 0 ≤ s) (hs : s < serviceEnd input x r) :
    δ < mdPath input x r s r := by
  by_contra h
  push_neg at h
  have := csInf_le (serviceEnd_set_bdd hv hx hr) (show s ∈ {s : ℝ | 0 ≤ s ∧
    mdPath input x r s r ≤ δ} from ⟨hs0, h⟩)
  exact absurd hs (not_lt.mpr this)

theorem mdPath_serviceEnd : mdPath input x r (serviceEnd input x r) r = δ := by
  have hcont := mdPath_self_continuous (input := input) x r
  have hmem : serviceEnd input x r ∈ {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ} := by
    apply IsClosed.csInf_mem _ (serviceEnd_set_nonempty hv hx hr) (serviceEnd_set_bdd hv hx hr)
    exact isClosed_Ici.inter (isClosed_Iic.preimage hcont)
  apply le_antisymm hmem.2
  by_contra hlt
  push_neg at hlt
  have h0 := mdPath_zero hv hx hr
  have hpos : 0 < serviceEnd input x r := by
    rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h, h0] at hlt; linarith
    · exact h
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hpos.le hcont.continuousOn
    (show δ ∈ Set.Icc _ _ from ⟨hlt.le, by rw [h0]; exact hr.le⟩)
  rcases eq_or_lt_of_le hc.2 with h | h
  · rw [h] at hfc; linarith
  · have := delta_lt_mdPath hv hx hr hc.1 h
    try simp only at hfc
    linarith

theorem criticalState_self : criticalState input x r r = δ :=
  mdPath_serviceEnd hv hx hr

theorem criticalState_of_ne {i : Page} (hi : i ≠ r) :
    criticalState input x r i = evictCurve input x i (serviceEnd input x r) :=
  mdPath_of_ne x r _ hi

theorem le_criticalState {i : Page} (hi : i ≠ r) : x i ≤ criticalState input x r i := by
  rw [criticalState_of_ne hv hx hr hi]
  calc x i = evictCurve input x i 0 := (evictCurve_zero i (hx.1 i).2).symm
    _ ≤ _ := evictCurve_mono hv i (by linarith [(hx.1 i).1, delta_pos hv])
        (serviceEnd_nonneg hv hx hr)

theorem criticalState_isRest : IsRest input (criticalState input x r) := by
  refine ⟨fun i => ?_, ?_⟩
  · rcases eq_or_ne i r with rfl | hi
    · rw [criticalState_self hv hx hr]; exact ⟨le_rfl, (delta_lt_one hv).le⟩
    · refine ⟨(hx.1 i).1.trans (le_criticalState hv hx hr hi), ?_⟩
      rw [criticalState_of_ne hv hx hr hi]; exact evictCurve_le_one _ _ _
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
    have : ∀ j ∈ Finset.univ.erase r, criticalState input x r j =
        evictCurve input x j (serviceEnd input x r) := fun j hj =>
      criticalState_of_ne hv hx hr (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_congr rfl this]
    unfold criticalState
    rw [mdPath_self]
    ring

theorem criticalFetch_lt_weight : criticalFetch input x r < w r := by
  unfold criticalFetch
  have := hv.weight_pos r
  have := (hx.1 r).2
  have := delta_pos hv
  nlinarith

/-- The fetch cost of the critical service is its fetch. -/
theorem critical_fetchCost :
    ∑ i, w i * max 0 (x i - criticalState input x r i) = criticalFetch input x r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), criticalState_self hv hx hr]
  unfold criticalFetch
  rw [max_eq_right (by linarith)]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [max_eq_left (by linarith [le_criticalState hv hx hr (Finset.ne_of_mem_erase hi)]), mul_zero]

/-- `∑ wᵢ xᵢ` changes by `EV - fetch` in a critical service. -/
theorem critical_weightedMass :
    ∑ i, w i * criticalState input x r i =
      ∑ i, w i * x i + criticalEV input x r - criticalFetch input x r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), ← Finset.add_sum_erase _ _ (Finset.mem_univ r),
    criticalState_self hv hx hr]
  unfold criticalFetch criticalEV
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Critical.DivergenceAux` -/
section

/-!
# Auxiliary facts for `Divergence.lean`

Right derivatives of the eviction curves and a comparison principle for functions with right derivatives.
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

open Set

set_option linter.unusedSectionVars false

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- Page `i` is not yet evicted at path time `u`. -/
abbrev NotEvicted (input : Instance Page) (x : Page → ℝ) (i : Page) (u : ℝ) : Prop :=
  x i * Real.exp (u / w i) < 1

theorem dvEvictCurve_of_notEvicted {x : Page → ℝ} {i : Page} {u : ℝ}
    (h : NotEvicted input x i u) :
    evictCurve input x i u = x i * Real.exp (u / w i) := min_eq_right h.le

theorem dvEvictCurve_of_evicted {x : Page → ℝ} {i : Page} {u : ℝ}
    (h : ¬ NotEvicted input x i u) : evictCurve input x i u = 1 :=
  min_eq_left (not_lt.mp h)

theorem dvEvictCurve_zero {x : Page → ℝ} {i : Page} (h : x i ≤ 1) :
    evictCurve input x i 0 = x i := by
  simp [evictCurve, h]

theorem dvEvictCurve_pos {x : Page → ℝ} {i : Page} (h : 0 < x i) (s : ℝ) :
    0 < evictCurve input x i s :=
  lt_min one_pos (mul_pos h (Real.exp_pos _))

theorem dvEvictCurve_continuous (x : Page → ℝ) (i : Page) :
    Continuous (evictCurve input x i) := by
  unfold evictCurve
  fun_prop

/-- The right derivative of an eviction curve. -/
theorem dvEvictCurve_hasDerivWithinAt {x : Page → ℝ} {i : Page} (hw : 0 < w i)
    (hx : 0 ≤ x i) (u : ℝ) :
    HasDerivWithinAt (evictCurve input x i)
      (if NotEvicted input x i u then evictCurve input x i u / w i else 0)
      (Ici u) u := by
  split_ifs with h
  · have hd : HasDerivAt (fun s => x i * Real.exp (s / w i))
        (x i * Real.exp (u / w i) / w i) u := by
      have := (((hasDerivAt_id u).div_const (w i)).exp).const_mul (x i)
      refine this.congr_deriv ?_
      simp only [id]
      ring
    have hc : Continuous fun s => x i * Real.exp (s / w i) := by fun_prop
    have hev : evictCurve input x i =ᶠ[nhds u] fun s => x i * Real.exp (s / w i) := by
      filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with s hs
      exact min_eq_right hs.le
    rw [dvEvictCurve_of_notEvicted h]
    exact (hd.congr_of_eventuallyEq hev).hasDerivWithinAt
  · have h1 : ∀ s ∈ Ici u, evictCurve input x i s = 1 := by
      intro s hs
      apply min_eq_left
      have h' : 1 ≤ x i * Real.exp (u / w i) := not_lt.mp h
      refine h'.trans (mul_le_mul_of_nonneg_left ?_ hx)
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs hw.le)
    exact (hasDerivWithinAt_const u (Ici u) (1 : ℝ)).congr h1 (h1 u self_mem_Ici)

/-- Comparison principle: if `f' ≤ B'` on `[a, b)` (right derivatives), then `f b - f a ≤ B b - B a`. -/
theorem sub_le_sub_of_deriv_right_le {f f' B B' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hf' : ∀ u, HasDerivWithinAt f (f' u) (Ici u) u)
    (hB : Continuous B) (hB' : ∀ u, HasDerivWithinAt B (B' u) (Ici u) u)
    (bound : ∀ u ∈ Ico a b, f' u ≤ B' u) : f b - f a ≤ B b - B a := by
  have := image_le_of_deriv_right_le_deriv_boundary (f := f) (f' := f') (a := a) (b := b)
    hf.continuousOn (fun u _ => hf' u) (B := fun s => B s - B a + f a) (B' := B')
    (by simp) (by fun_prop) (fun u _ => (hB' u).sub_const _ |>.add_const _) bound
    ⟨hab, le_rfl⟩
  linarith

/-- Comparison with a linear function. -/
theorem sub_le_mul_of_deriv_right_le {f f' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hf' : ∀ u, HasDerivWithinAt f (f' u) (Ici u) u)
    (bound : ∀ u ∈ Ico a b, f' u ≤ c) : f b - f a ≤ c * (b - a) := by
  have := sub_le_sub_of_deriv_right_le (B := fun s => c * s) (B' := fun _ => c) hab hf hf'
    (by fun_prop) (fun u => ((hasDerivAt_id u).const_mul c).hasDerivWithinAt.congr_deriv
      (by simp)) bound
  try simp only at this
  linarith

theorem dvMin_sub_min_le {a b S : ℝ} (h : b ≤ a) : min a S - min b S ≤ a - b := by
  simp only [min_def]; split_ifs <;> linarith

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Critical.Divergence` -/
section

/-!
# The Bregman potential (`sec:bregman`)

`D(O ‖ x) = ∑_{i ∉ O} wᵢ g(xᵢ) + ∑_{i ∈ O} wᵢ xᵢ` with `g(u) = u - 1 - ln u`, its behaviour under moves of the comparator (`lem:optmoves`) and in one critical service (`prop:phaseD`).
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- `g(u) = u - 1 - ln u`. -/
noncomputable def bregG (u : ℝ) : ℝ := u - 1 - Real.log u

/-- The Bregman divergence `D(O ‖ x)`. -/
noncomputable def divergence (input : Instance Page) (O : Finset Page) (x : Page → ℝ) : ℝ :=
  ∑ i, w i * (if i ∈ O then x i else bregG (x i))

theorem bregG_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ bregG u := by
  have := Real.log_le_sub_one_of_pos hu
  unfold bregG; linarith

theorem bregG_le_of_frac (hv : input.Valid) {u : ℝ} (h1 : δ ≤ u) :
    bregG u ≤ L - 1 + u := by
  have hd := delta_pos hv
  have : Real.log δ ≤ Real.log u := Real.log_le_log hd h1
  rw [log_delta hv] at this
  unfold bregG; linarith

theorem divergence_nonneg (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O : Finset Page) : 0 ≤ divergence input O x := by
  unfold divergence
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hv.weight_pos i).le ?_
  have hxi : 0 < x i := lt_of_lt_of_le (delta_pos hv) (hx i).1
  split_ifs
  · exact hxi.le
  · exact bregG_nonneg hxi

theorem divergence_le (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O : Finset Page) : divergence input O x ≤ (L + 1) * input.totalWeight := by
  unfold divergence Instance.totalWeight
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (L + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (hv.weight_pos i).le
  have hL := L_pos hv
  have h1 := (hx i).2
  split_ifs
  · linarith
  · have := bregG_le_of_frac hv (hx i).1
    linarith

/-- `lem:optmoves`, one comparator move: replacing `O` by `O'` changes `D` by at most `L` times the evicted weight plus the fetched weight. -/
theorem divergence_change_cache (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O O' : Finset Page) :
    divergence input O' x - divergence input O x ≤
      L * ∑ i ∈ O \ O', w i + ∑ i ∈ O' \ O, w i := by
  unfold divergence
  have e1 : ∀ T : Finset Page, ∑ i ∈ T, w i =
      ∑ i, if i ∈ T then w i else 0 := fun T => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [e1, e1, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw := (hv.weight_pos i).le
  have hL := L_pos hv
  have hxi : 0 < x i := lt_of_lt_of_le (delta_pos hv) (hx i).1
  have hlog : Real.log δ ≤ Real.log (x i) := Real.log_le_log (delta_pos hv) (hx i).1
  have hlog1 : Real.log (x i) ≤ 0 := Real.log_nonpos hxi.le (hx i).2
  rw [log_delta hv] at hlog
  by_cases h : i ∈ O <;> by_cases h' : i ∈ O' <;> simp [h, h', bregG] <;> nlinarith

/-! ### Auxiliary: the critical service part of `D` from the pages `i ≠ r` -/

section CriticalAux

open Set

/-- The contribution of the pages `i ≠ r` to `D(O ‖ x(s))` along the critical service. -/
noncomputable def restPart (input : Instance Page) (O : Finset Page) (x : Page → ℝ) (r : Page)
    (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i *
    (if i ∈ O then evictCurve input x i s else bregG (evictCurve input x i s))

/-- Its right derivative. -/
noncomputable def restDeriv (input : Instance Page) (O : Finset Page) (x : Page → ℝ) (r : Page)
    (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r,
    (if NotEvicted input x i u then evictCurve input x i u - (if i ∈ O then 0 else 1) else 0)

/-- The weighted missing mass of the pages `i ≠ r` along the critical service. -/
noncomputable def evMass (input : Instance Page) (x : Page → ℝ) (r : Page) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i * evictCurve input x i s

/-- Its right derivative. -/
noncomputable def evDeriv (input : Instance Page) (x : Page → ℝ) (r : Page) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, (if NotEvicted input x i u then evictCurve input x i u else 0)

theorem continuous_restPart {x : Page → ℝ} (hx0 : ∀ i, 0 < x i) (O : Finset Page) (r : Page) :
    Continuous (restPart input O x r) := by
  unfold restPart
  refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
  have hc := dvEvictCurve_continuous (input := input) x i
  by_cases hi : i ∈ O
  · simp only [hi, ↓reduceIte]; exact hc
  · simp only [hi, ↓reduceIte]
    unfold bregG
    exact (hc.sub continuous_const).sub (hc.log fun s => (dvEvictCurve_pos (hx0 i) s).ne')

theorem continuous_evMass (x : Page → ℝ) (r : Page) : Continuous (evMass input x r) := by
  unfold evMass
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (dvEvictCurve_continuous x i)

theorem hasDerivWithinAt_restPart (hv : input.Valid) {x : Page → ℝ} (hx0 : ∀ i, 0 < x i)
    (O : Finset Page) (r : Page) (u : ℝ) :
    HasDerivWithinAt (restPart input O x r) (restDeriv input O x r u) (Ici u) u := by
  unfold restPart restDeriv
  refine HasDerivWithinAt.fun_sum fun i _ => ?_
  have hw := hv.weight_pos i
  have hd := dvEvictCurve_hasDerivWithinAt (input := input) (x := x) hw (hx0 i).le u
  have hpos := dvEvictCurve_pos (input := input) (hx0 i) u
  by_cases hi : i ∈ O
  · simp only [hi, ↓reduceIte]
    refine (hd.const_mul _).congr_deriv ?_
    split_ifs <;> field_simp <;> simp
  · simp only [hi, ↓reduceIte]
    have h2 : HasDerivWithinAt (fun s => w i * bregG (evictCurve input x i s))
        (w i * ((if NotEvicted input x i u then evictCurve input x i u / w i
          else 0) - (if NotEvicted input x i u then evictCurve input x i u / w i
          else 0) / evictCurve input x i u)) (Ici u) u := by
      unfold bregG
      exact ((hd.sub_const 1).sub (hd.log hpos.ne')).const_mul _
    refine h2.congr_deriv ?_
    split_ifs
    · field_simp
    · simp

theorem hasDerivWithinAt_evMass (hv : input.Valid) {x : Page → ℝ} (hx0 : ∀ i, 0 < x i)
    (r : Page) (u : ℝ) :
    HasDerivWithinAt (evMass input x r) (evDeriv input x r u) (Ici u) u := by
  unfold evMass evDeriv
  refine HasDerivWithinAt.fun_sum fun i _ => ?_
  have hw := hv.weight_pos i
  have hd := dvEvictCurve_hasDerivWithinAt (input := input) (x := x) hw (hx0 i).le u
  refine (hd.const_mul _).congr_deriv ?_
  split_ifs
  · field_simp
  · simp

theorem dvMdPath_self_eq (x : Page → ℝ) (r : Page) (u : ℝ) :
    mdPath input x r u r = restMass input - ∑ j ∈ Finset.univ.erase r, evictCurve input x j u := by
  simp [mdPath]

/-- The key identity `h(u) = [r ∉ O] - x_r(u) - |E(u) ∩ O|`. -/
theorem restDeriv_eq {O : Finset Page} (hO : O.card = k) (x : Page → ℝ) (r : Page)
    (u : ℝ) :
    restDeriv input O x r u = (if r ∈ O then 0 else 1) - mdPath input x r u r -
      ∑ i ∈ Finset.univ.erase r, (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
  have ht : ∀ i, (if NotEvicted input x i u then
      evictCurve input x i u - (if i ∈ O then 0 else 1) else 0) =
      (evictCurve input x i u - (if i ∈ O then 0 else 1)) -
        (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
    intro i
    by_cases h : NotEvicted input x i u
    · simp [h]
    · rw [dvEvictCurve_of_evicted h]
      by_cases hi : i ∈ O <;> simp [h, hi]
  unfold restDeriv
  rw [Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    dvMdPath_self_eq]
  have h2 : ∑ i, (if i ∈ O then (0 : ℝ) else 1) = restMass input := by
    have : ∀ i, (if i ∈ O then (0 : ℝ) else 1) = 1 - (if i ∈ O then 1 else 0) := by
      intro i; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
    simp [restMass, hO]
  have h1 := Finset.add_sum_erase Finset.univ (fun i => if i ∈ O then (0 : ℝ) else 1)
    (Finset.mem_univ r)
  try simp only at h1
  linarith

theorem divergence_eq_split (O : Finset Page) (y : Page → ℝ) (r : Page) :
    divergence input O y = w r * (if r ∈ O then y r else bregG (y r)) +
      ∑ i ∈ Finset.univ.erase r, w i * (if i ∈ O then y i else bregG (y i)) :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm

theorem divergence_start {x : Page → ℝ} (hx : IsRest input x) (O : Finset Page) (r : Page) :
    divergence input O x = w r * (if r ∈ O then x r else bregG (x r)) +
      restPart input O x r 0 := by
  rw [divergence_eq_split O x r]
  congr 1
  unfold restPart
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dvEvictCurve_zero (hx.1 i).2]

theorem divergence_end (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
    (hr : δ < x r) (O : Finset Page) :
    divergence input O (criticalState input x r) =
      w r * (if r ∈ O then δ else bregG δ) +
      restPart input O x r (serviceEnd input x r) := by
  rw [divergence_eq_split O _ r, criticalState_self hv hx hr]
  congr 1
  unfold restPart
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [criticalState_of_ne hv hx hr (Finset.ne_of_mem_erase hi)]

end CriticalAux

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
  (hr : δ < x r) {O : Finset Page} (hO : O.card = k)
include hv hx hr hO

/-- `prop:phaseD`, hit service. -/
theorem critical_hit (hrO : r ∈ O) :
    divergence input O (criticalState input x r) - divergence input O x ≤ -criticalFetch input x r := by
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_lt_of_le (delta_pos hv) (hx.1 i).1
  have hS0 := serviceEnd_nonneg hv hx hr
  have hD0 := divergence_start hx O r
  have hD1 := divergence_end hv hx hr O
  have hA := sub_le_mul_of_deriv_right_le (c := 0) hS0 (continuous_restPart hx0 O r)
    (hasDerivWithinAt_restPart hv hx0 O r) fun u hu => by
      have hxr := delta_lt_mdPath hv hx hr hu.1 hu.2
      have hd := delta_pos hv
      rw [restDeriv_eq hO, if_pos hrO]
      have : 0 ≤ ∑ i ∈ Finset.univ.erase r,
          (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
      linarith
  rw [hD0, hD1]
  simp only [hrO, ↓reduceIte]
  unfold criticalFetch
  linarith

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Critical` -/
section

/-!
# One critical service, deposits and overshoots

Pure facts (no run, no log) about the critical service for a valid instance `input`, and about the deposits and overshoots of `PMD`.

* `serviceEnd_le_add_serviceEnd` (`lem:drop`): after a critical service on `p ≠ q`, the critical service on `q` is shorter by at most `|λ_p(x)|`; `serviceEnd_le_chainLen_add` iterates it along a chain of critical services.
* `serviceEnd_le_three_mul_criticalEV` (`lem:clock`): `|λ| ≤ 3 EV(λ)`.
* `serviceEnd_le_of_light`: if the pages of level `≤ e` hold cached mass at least `1 - δ`, every critical service has length at most `L 2^e`.
* `levelLen` facts: `0 ≤ |λ|_W ≤ L W`, telescoping, `∑_W |λ|_W ≤ |λ|`.
* Overshoots: `o_q ≥ 0` and `delay_q ≤ c_q + w_q + o_q`.

`serviceEnd` and `criticalState` apply to arbitrary `x`; from a rest state with `x_p ≤ δ` the critical service is trivial (length `0`, state unchanged: `serviceEnd_eq_zero_of_le`, `criticalState_eq_of_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  mdPath evictCurve restMass IsRest IsFrac criticalEV evMass evDeriv NotEvicted levelWeight_pos
  levelWeight_succ sum_Icc_telescope' dvMin_sub_min_le)

/-! ### Basic facts about one critical service -/

section Deadline

variable {input : Instance Page}

/-- `|λ_p(x)| ≥ 0`, for every `x`. -/
theorem C.serviceEnd_nonneg' (x : Page → ℝ) (p : Page) : 0 ≤ serviceEnd input x p :=
  Real.sInf_nonneg fun _ hs => hs.1

/-- The critical service on `p` ends no later than any `s ≥ 0` with `x_p(s) ≤ δ`. -/
theorem serviceEnd_le_of_mem {x : Page → ℝ} {p : Page} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : mdPath input x p s p ≤ δ) : serviceEnd input x p ≤ s :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨hs0, hs⟩

theorem mdPath_zero_self' {x : Page → ℝ} (hx : IsRest input x) (p : Page) :
    mdPath input x p 0 p = x p := by
  rw [PagingWithDelay.PMD.mdPath_self, ← hx.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  rw [Finset.sum_congr rfl fun j _ =>
    PagingWithDelay.PMD.evictCurve_zero (input := input) j (hx.1 j).2]
  ring

theorem mdPath_zero' {x : Page → ℝ} (hx : IsRest input x) (p : Page) : mdPath input x p 0 = x := by
  funext i
  by_cases hi : i = p
  · subst hi; exact mdPath_zero_self' hx i
  · rw [PagingWithDelay.PMD.mdPath_of_ne _ _ _ hi,
      PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2]

/-- A critical service on a page with `x_p ≤ δ` has length `0`. -/
theorem serviceEnd_eq_zero_of_le {x : Page → ℝ} (hx : IsRest input x) {p : Page}
    (hp : x p ≤ δ) : serviceEnd input x p = 0 :=
  le_antisymm (serviceEnd_le_of_mem le_rfl (by rw [mdPath_zero_self' hx]; exact hp))
    (C.serviceEnd_nonneg' x p)

/-- A critical service on a page with `x_p ≤ δ` does not change the state. -/
theorem criticalState_eq_of_le {x : Page → ℝ} (hx : IsRest input x) {p : Page}
    (hp : x p ≤ δ) : criticalState input x p = x := by
  unfold criticalState
  rw [serviceEnd_eq_zero_of_le hx hp, mdPath_zero' hx]

section Valid

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
include hv hx

/-- A critical service from a rest state ends in a rest state (also when `x_p ≤ δ`). -/
theorem criticalState_isRest' (p : Page) : IsRest input (criticalState input x p) := by
  by_cases hp : δ < x p
  · exact PagingWithDelay.PMD.criticalState_isRest hv hx hp
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]; exact hx

/-- The other pages do not decrease (also when `x_p ≤ δ`). -/
theorem le_criticalState' {p q : Page} (hqp : q ≠ p) : x q ≤ criticalState input x p q := by
  by_cases hp : δ < x p
  · exact PagingWithDelay.PMD.le_criticalState hv hx hp hqp
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]

theorem delta_lt_criticalState {p q : Page} (hqp : q ≠ p) (hq : δ < x q) :
    δ < criticalState input x p q :=
  hq.trans_le (le_criticalState' hv hx hqp)

/-- The critical service on `p` does not increase `x_p` (it ends at `δ`, or does nothing when `x_p ≤ δ`). -/
theorem criticalState_self_le (p : Page) : criticalState input x p p ≤ x p := by
  by_cases hp : δ < x p
  · rw [PagingWithDelay.PMD.criticalState_self hv hx hp]; exact hp.le
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]

end Valid

/-- Continuing an eviction curve: if `y_i` is the eviction curve of `i` from `x` at time `a`, then the eviction curve of `i` from `y` at time `s ≥ 0` is the one from `x` at time `a + s` (once at `1`, it stays there). -/
theorem evictCurve_continue {x y : Page → ℝ} {i : Page} {a s : ℝ}
    (hy : y i = evictCurve input x i a) (hs : 0 ≤ s) :
    evictCurve input y i s = evictCurve input x i (a + s) := by
  have he : 1 ≤ Real.exp (s / w i) :=
    Real.one_le_exp (div_nonneg hs (input.weight_pos i).le)
  unfold evictCurve at hy ⊢
  rw [hy, add_div, Real.exp_add, ← mul_assoc]
  rcases le_total 1 (x i * Real.exp (a / w i)) with h | h
  · rw [min_eq_left h, one_mul, min_eq_left he,
      min_eq_left (one_le_mul_of_one_le_of_one_le h he)]
  · rw [min_eq_right h]

/-- The eviction curve is monotone in the start value and in time. -/
theorem evictCurve_le_of_le {x y : Page → ℝ} {i : Page} {s t : ℝ} (hyx : y i ≤ x i)
    (hx0 : 0 ≤ x i) (hst : s ≤ t) : evictCurve input y i s ≤ evictCurve input x i t := by
  unfold evictCurve
  apply min_le_min_left
  calc y i * Real.exp (s / w i) ≤ x i * Real.exp (s / w i) :=
        mul_le_mul_of_nonneg_right hyx (Real.exp_pos _).le
    _ ≤ x i * Real.exp (t / w i) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hst (input.weight_pos i).le)) hx0

/-! ### `lem:drop` -/

section Drop

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
include hv hx

/-- **`lem:drop`**: after the critical service on `p ≠ q` from the rest state `x`, the critical service on `q` is shorter by at most the length of the one on `p`: `|λ_q(x)| ≤ |λ_p(x)| + |λ_q(x̃)|`. No assumption on `x_p` is needed (for `x_p ≤ δ` the service on `p` is trivial).

As in the paper, let `λ = λ_{x→q}`, `λ̃ = λ_{x̃→q}` and `a = |λ_{x→p}|`. For pages `i ∉ {p, q}`, `λ̃` continues the path of the service on `p`: `λ̃(s)_i = λ(s + a)_i`. For `p`, `λ̃(s)_p ≤ λ(s)_p ≤ λ(s + a)_p` as `x̃_p ≤ x_p`. Summing over `i ≠ q` at `s = |λ̃|` gives `λ(|λ̃| + a)_q ≤ λ̃(|λ̃|)_q = δ`, so `|λ| ≤ |λ̃| + a` (`|λ|` is the first time with `λ_q ≤ δ`). -/
theorem serviceEnd_le_add_serviceEnd {p q : Page} (hpq : p ≠ q) (hq : δ < x q) :
    serviceEnd input x q ≤ serviceEnd input x p + serviceEnd input (criticalState input x p) q := by
  set a := serviceEnd input x p with ha_def
  set s := serviceEnd input (criticalState input x p) q with hs_def
  have ha : 0 ≤ a := C.serviceEnd_nonneg' x p
  have hs : 0 ≤ s := C.serviceEnd_nonneg' _ q
  have hy := criticalState_isRest' hv hx p
  have hyq := delta_lt_criticalState hv hx hpq.symm hq
  -- pages `i ∉ {p, q}`: `λ̃(s)_i = λ(s + a)_i`
  have hcont : ∀ i, i ≠ p →
      evictCurve input (criticalState input x p) i s = evictCurve input x i (a + s) := fun i hip =>
    evictCurve_continue (show criticalState input x p i = evictCurve input x i a from
      PagingWithDelay.PMD.mdPath_of_ne x p a hip) hs
  -- page `p`: `λ̃(s)_p ≤ λ(s)_p ≤ λ(s + a)_p`
  have hp : evictCurve input (criticalState input x p) p s ≤ evictCurve input x p (a + s) := by
    have hx0 : 0 ≤ x p := le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 p).1
    calc evictCurve input (criticalState input x p) p s ≤ evictCurve input x p s :=
          evictCurve_le_of_le (criticalState_self_le hv hx p) hx0 le_rfl
      _ ≤ evictCurve input x p (a + s) := evictCurve_le_of_le le_rfl hx0 (by linarith)
  have hsum : ∑ i ∈ Finset.univ.erase q, evictCurve input (criticalState input x p) i s ≤
      ∑ i ∈ Finset.univ.erase q, evictCurve input x i (a + s) :=
    Finset.sum_le_sum fun i _ => by
      by_cases hip : i = p
      · subst hip; exact hp
      · exact (hcont i hip).le
  -- hence `λ(s + a)_q ≤ λ̃(s)_q = δ`
  apply serviceEnd_le_of_mem (add_nonneg ha hs)
  have h1 := PagingWithDelay.PMD.mdPath_serviceEnd hv hy hyq
  rw [PagingWithDelay.PMD.mdPath_self] at h1 ⊢
  linarith

end Drop

/-! ### Chains of critical services -/

variable (input) in
/-- The state after the critical services on the pages of `ps`, in order, from `x`. -/
noncomputable def chainState (x : Page → ℝ) : List Page → Page → ℝ
  | [] => x
  | p :: ps => chainState (criticalState input x p) ps

variable (input) in
/-- The total length of the critical services on the pages of `ps`, in order, from `x`. -/
noncomputable def chainLen (x : Page → ℝ) : List Page → ℝ
  | [] => 0
  | p :: ps => serviceEnd input x p + chainLen (criticalState input x p) ps

@[simp] theorem chainState_nil (x : Page → ℝ) : chainState input x [] = x := rfl

@[simp] theorem chainState_cons (x : Page → ℝ) (p : Page) (ps : List Page) :
    chainState input x (p :: ps) = chainState input (criticalState input x p) ps := rfl

@[simp] theorem chainLen_nil (x : Page → ℝ) : chainLen input x [] = 0 := rfl

@[simp] theorem chainLen_cons (x : Page → ℝ) (p : Page) (ps : List Page) :
    chainLen input x (p :: ps) = serviceEnd input x p + chainLen input (criticalState input x p) ps := rfl

theorem chainLen_nonneg (x : Page → ℝ) : ∀ ps : List Page, 0 ≤ chainLen input x ps
  | [] => le_rfl
  | p :: ps => add_nonneg (C.serviceEnd_nonneg' x p) (chainLen_nonneg _ ps)

theorem chainState_isRest (hv : input.Valid) :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → IsRest input (chainState input x ps)
  | [], _, hx => hx
  | p :: ps, _, hx => chainState_isRest hv ps (criticalState_isRest' hv hx p)

theorem delta_lt_chainState (hv : input.Valid) {q : Page} :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → q ∉ ps → δ < x q →
      δ < chainState input x ps q
  | [], _, _, _, hq => hq
  | p :: ps, _, hx, hqs, hq => by
    simp only [List.mem_cons, not_or] at hqs
    exact delta_lt_chainState hv ps (criticalState_isRest' hv hx p) hqs.2
      (delta_lt_criticalState hv hx hqs.1 hq)

/-- **`lem:drop`, iterated**: after a chain of critical services on pages other than `q`, the critical service on `q` is shorter by at most the total length of the chain. -/
theorem serviceEnd_le_chainLen_add (hv : input.Valid) {q : Page} :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → q ∉ ps → δ < x q →
      serviceEnd input x q ≤ chainLen input x ps + serviceEnd input (chainState input x ps) q
  | [], _, _, _, _ => by simp
  | p :: ps, x, hx, hqs, hq => by
    simp only [List.mem_cons, not_or] at hqs
    have h1 := serviceEnd_le_add_serviceEnd hv hx (Ne.symm hqs.1) hq
    have h2 := serviceEnd_le_chainLen_add hv ps (criticalState_isRest' hv hx p) hqs.2
      (delta_lt_criticalState hv hx hqs.1 hq)
    simp only [chainLen_cons, chainState_cons]
    linarith

/-! ### `lem:clock` -/

/-- `k δ = k/(2k+1) ≥ 1/3`. -/
theorem one_third_le_cacheSize_mul_delta (hv : input.Valid) :
    1 / 3 ≤ (k : ℝ) * δ := by
  unfold Instance.delta
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

section Clock

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {p : Page} (hp : δ < x p)
include hv hx hp

/-- Before the end of the critical service the weighted eviction rate is at least `k δ ≥ 1/3`, as at most `n - k - 1` of the pages `i ≠ p` are fully evicted. -/
theorem one_third_le_evDeriv {u : ℝ} (hu0 : 0 ≤ u) (hu : u < serviceEnd input x p) :
    1 / 3 ≤ evDeriv input x p u := by
  set N := (Finset.univ.erase p).filter (fun i => NotEvicted input x i u) with hN
  set M := (Finset.univ.erase p).filter (fun i => ¬ NotEvicted input x i u) with hM
  have hcard : N.card + M.card = (Finset.univ.erase p).card :=
    Finset.card_filter_add_card_filter_not _
  have hcard2 : (Finset.univ.erase p).card + 1 = Fintype.card Page :=
    Finset.card_erase_add_one (Finset.mem_univ p)
  have hge : ∀ i, x i ≤ evictCurve input x i u := fun i => by
    calc x i = evictCurve input x i 0 := (PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2).symm
      _ ≤ _ := PagingWithDelay.PMD.evictCurve_mono hv i
          (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 i).1) hu0
  -- the evicted pages
  have hMsum : (M.card : ℝ) ≤ ∑ j ∈ Finset.univ.erase p, evictCurve input x j u := by
    have h1 : ∑ j ∈ M, evictCurve input x j u = M.card := by
      rw [Finset.sum_congr rfl fun j hj =>
        PagingWithDelay.PMD.dvEvictCurve_of_evicted (Finset.mem_filter.mp hj).2]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ _
    exact le_trans (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 j).1) (hge j)
  have hlt := PagingWithDelay.PMD.delta_lt_mdPath hv hx hp hu0 hu
  rw [PagingWithDelay.PMD.mdPath_self] at hlt
  unfold restMass at hlt
  have hk : (k : ℝ) < N.card + 1 := by
    have hc : ((N.card : ℕ) : ℝ) + M.card + 1 = Fintype.card Page := by
      exact_mod_cast (show N.card + M.card + 1 = Fintype.card Page by omega)
    linarith [PagingWithDelay.PMD.delta_pos hv]
  have hk' : (k : ℝ) ≤ N.card := by
    have : k < N.card + 1 := by exact_mod_cast hk
    exact_mod_cast (show k ≤ N.card by omega)
  have hD : evDeriv input x p u = ∑ j ∈ N, evictCurve input x j u := by
    unfold evDeriv
    rw [hN, Finset.sum_filter]
  have hDge : (N.card : ℝ) * δ ≤ evDeriv input x p u := by
    rw [hD]
    have : ∑ j ∈ N, δ ≤ ∑ j ∈ N, evictCurve input x j u :=
      Finset.sum_le_sum fun j _ => (hx.1 j).1.trans (hge j)
    simpa using this
  have := one_third_le_cacheSize_mul_delta hv
  nlinarith [PagingWithDelay.PMD.delta_pos hv]

/-- `EV(λ) = G(s^end) - G(0)` for `G(s) = ∑_{i ≠ p} wᵢ xᵢ(s)`. -/
theorem criticalEV_eq_evMass :
    criticalEV input x p = evMass input x p (serviceEnd input x p) - evMass input x p 0 := by
  unfold criticalEV evMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PagingWithDelay.PMD.criticalState_of_ne hv hx hp (Finset.ne_of_mem_erase hi),
    PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2, mul_sub]

/-- **`lem:clock`**: `|λ| ≤ 3 EV(λ)`. -/
theorem serviceEnd_le_three_mul_criticalEV : serviceEnd input x p ≤ 3 * criticalEV input x p := by
  have hx0 : ∀ i, 0 < x i := fun i => (PagingWithDelay.PMD.delta_pos hv).trans_le (hx.1 i).1
  have h := PagingWithDelay.PMD.sub_le_mul_of_deriv_right_le
    (f := fun s => -evMass input x p s) (f' := fun u => -evDeriv input x p u) (c := -(1 / 3))
    (PagingWithDelay.PMD.serviceEnd_nonneg hv hx hp)
    (PagingWithDelay.PMD.continuous_evMass x p).neg
    (fun u => (PagingWithDelay.PMD.hasDerivWithinAt_evMass hv hx0 p u).neg)
    (fun u hu => neg_le_neg (one_third_le_evDeriv hv hx hp hu.1 hu.2))
  rw [criticalEV_eq_evMass hv hx hp]
  try simp only at h
  linarith

end Clock

/-! ### Light mass ⇒ short service -/

/-- If the pages of level `≤ e` hold cached mass `∑_{i : wᵢ ≤ 2^e} (1 - xᵢ) ≥ 1 - δ` (the second half of `preemptCondition`), then every critical service from the rest state `x` has length at most `L 2^e`: by then the pages `i ≠ q` of level `≤ e` are fully evicted, having gained at least `x_q - δ`. -/
theorem serviceEnd_le_of_light (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) (q : Page)
    {e : ℤ} (hcond : 1 - δ ≤
      ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) :
    serviceEnd input x q ≤ L * levelWeight e := by
  have hL := PagingWithDelay.PMD.L_pos hv
  have hW := levelWeight_pos e
  apply serviceEnd_le_of_mem (by positivity)
  rw [PagingWithDelay.PMD.mdPath_self]
  set f : Page → ℝ := fun j => if level input j ≤ e then 1 - x j else 0 with hf
  have hterm : ∀ j, x j + f j ≤ evictCurve input x j (L * levelWeight e) := by
    intro j
    simp only [hf]
    split_ifs with hj
    · have : evictCurve input x j (L * levelWeight e) = 1 := by
        unfold evictCurve
        apply min_eq_left
        have hwj := hv.weight_pos j
        have hle : w j ≤ levelWeight e :=
          (PagingWithDelay.PMD.level_le_iff hv j e).mp hj
        have hge : L ≤ L * levelWeight e / w j := by
          rw [le_div_iff₀ hwj]
          exact mul_le_mul_of_nonneg_left hle hL.le
        calc (1 : ℝ) = δ * Real.exp L :=
              (PagingWithDelay.PMD.delta_mul_exp_L hv).symm
          _ ≤ x j * Real.exp (L * levelWeight e / w j) := by
            apply mul_le_mul (hx.1 j).1 (Real.exp_le_exp.mpr hge) (Real.exp_pos _).le
            linarith [(hx.1 j).1, PagingWithDelay.PMD.delta_pos hv]
      rw [this]; ring_nf; exact le_rfl
    · rw [add_zero]
      calc x j = evictCurve input x j 0 := (PagingWithDelay.PMD.evictCurve_zero j (hx.1 j).2).symm
        _ ≤ _ := PagingWithDelay.PMD.evictCurve_mono hv j
            (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 j).1) (by positivity)
  have hsum : ∑ j ∈ Finset.univ.erase q, (x j + f j) ≤
      ∑ j ∈ Finset.univ.erase q, evictCurve input x j (L * levelWeight e) :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [Finset.sum_add_distrib] at hsum
  have hx2 := hx.2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)] at hx2
  have hf2 : ∑ j, f j = ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i) := by
    simp only [hf]; rw [Finset.sum_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)] at hf2
  have hfq : f q ≤ 1 - x q := by
    simp only [hf]; split_ifs <;> linarith [(hx.1 q).2]
  linarith

/-- `serviceEnd_le_of_light` under the condition of a level-`e` preemptive service. -/
theorem serviceEnd_le_of_preemptCondition (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
    (q : Page) {budget : ℤ → ℝ} {e : ℤ}
    (h : PagingWithDelay.PMD.preemptCondition input x budget e) :
    serviceEnd input x q ≤ L * levelWeight e :=
  serviceEnd_le_of_light hv hx q h.2

end Deadline

/-! ### Deposits: `levelLen` -/

section LevelLen

variable {input : Instance Page}

/-- `L = ln (2k+1) ≥ 0` (no assumptions needed). -/
theorem L_nonneg' (input : Instance Page) : 0 ≤ L :=
  Real.log_nonneg (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)

/-- `|λ|_W = min (L·2W) |λ| - min (L·W) |λ|`, written with `levelWeight (e+1) = 2W`. -/
theorem levelLen_eq_sub (x : Page → ℝ) (p : Page) (e : ℤ) :
    levelLen input x p e = min (L * levelWeight (e + 1)) (serviceEnd input x p) -
      min (L * levelWeight e) (serviceEnd input x p) := by
  unfold levelLen
  rw [levelWeight_succ, show L * (2 * levelWeight e) = 2 * L * levelWeight e by ring]

theorem C.levelLen_nonneg (x : Page → ℝ) (p : Page) (e : ℤ) : 0 ≤ levelLen input x p e := by
  unfold levelLen
  apply sub_nonneg.mpr
  apply min_le_min_right
  have := L_nonneg' input
  have := levelWeight_pos e
  nlinarith

theorem levelLen_le (x : Page → ℝ) (p : Page) (e : ℤ) :
    levelLen input x p e ≤ L * levelWeight e := by
  unfold levelLen
  have := L_nonneg' input
  have := levelWeight_pos e
  have h := dvMin_sub_min_le (a := 2 * L * levelWeight e) (b := L * levelWeight e)
    (S := serviceEnd input x p) (by nlinarith)
  linarith

/-- Telescoping: `∑_{a ≤ e ≤ b} |λ|_{2^e} = min (L 2^{b+1}) |λ| - min (L 2^a) |λ|`. -/
theorem sum_levelLen_Icc (x : Page → ℝ) (p : Page) {a b : ℤ} (hab : a ≤ b) :
    ∑ e ∈ Finset.Icc a b, levelLen input x p e =
      min (L * levelWeight (b + 1)) (serviceEnd input x p) -
        min (L * levelWeight a) (serviceEnd input x p) := by
  simp_rw [levelLen_eq_sub]
  exact sum_Icc_telescope' (fun e => min (L * levelWeight e) (serviceEnd input x p))
    a b hab

/-- The intervals `I_W` are disjoint: `∑_{a ≤ e ≤ b} |λ|_{2^e} ≤ |λ|`. -/
theorem sum_levelLen_Icc_le (x : Page → ℝ) (p : Page) (a b : ℤ) :
    ∑ e ∈ Finset.Icc a b, levelLen input x p e ≤ serviceEnd input x p := by
  rcases lt_or_ge b a with h | h
  · rw [Finset.Icc_eq_empty (not_le.mpr h), Finset.sum_empty]
    exact C.serviceEnd_nonneg' _ _
  rw [sum_levelLen_Icc x p h]
  have h1 := min_le_right (L * levelWeight (b + 1)) (serviceEnd input x p)
  have h2 : 0 ≤ min (L * levelWeight a) (serviceEnd input x p) :=
    le_min (mul_nonneg (L_nonneg' input) (levelWeight_pos a).le) (C.serviceEnd_nonneg' _ _)
  linarith

/-- The total deposit of a critical service is at most its length. -/
theorem sum_levelLen_le (x : Page → ℝ) (p : Page) :
    ∑ e ∈ Finset.Icc (level input p) (maxLevel input), levelLen input x p e ≤
      serviceEnd input x p :=
  sum_levelLen_Icc_le x p _ _

end LevelLen

/-! ### Overshoots -/

section Overshoots

variable (input : Instance Page) (x : Page → ℝ) (pending : List (Request Page))
  (claims : Page → ℝ) (t : ℝ)

theorem C.overshoot_nonneg (q : Page) : 0 ≤ overshoot input pending claims q t :=
  le_max_left _ _

theorem le_overshoot_add (q : Page) :
    pageDelay pending q t ≤ claims q + w q + overshoot input pending claims q t := by
  unfold overshoot
  have := le_max_right 0 (pageDelay pending q t - claims q - w q)
  linarith

theorem C.mem_lighter {p q : Page} : q ∈ lighter input p ↔ w q ≤ w p := by
  simp [lighter]

theorem C.self_mem_lighter (p : Page) : p ∈ lighter input p := (C.mem_lighter input).mpr le_rfl

end Overshoots

end PMD

end PagingWithDelay
end

/-! ## Inlined from `Milestones.Bridge` -/
section

/-!
# Dictionary between the platform's path definitions and `PagingWithDelay`

For `n` pages, cache size `1 ≤ k < n` and positive weights `w`, `inst` is an instance of the
authors' formalization (with an arbitrary initial cache and no requests). The platform's
`path`, `pathLength`, `pathEnd`, `StateValid`, `delta`, `logFactor` are `mdPath`, `serviceEnd`,
`criticalState`, `IsRest`, `δ`, `L` of this instance.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PagingDelay.PMD.Bridge

open PagingDelay.PMD

lemma exists_initialCache (n k : ℕ) (hkn : k < n) :
    ∃ C : Finset (Fin n), C.card = k := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := k) (by simpa using hkn.le)
  exact ⟨t, ht⟩

/-- The authors' instance for `n` pages, cache size `k` and weights `w`, without requests. -/
noncomputable def inst (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) : PagingWithDelay.Instance (Fin n) where
  weight := w
  weight_pos := hw
  cacheSize := k
  cacheSize_pos := hk
  cacheSize_lt := by simpa using hkn
  initialCache := Classical.choose (exists_initialCache n k hkn)
  initialCache_card := Classical.choose_spec (exists_initialCache n k hkn)
  requests := []

lemma weight_pos_of_PMDWeights {n : ℕ} {w : Fin n → ℝ} (hw : PMDWeights w) (i : Fin n) :
    0 < w i := by
  obtain ⟨m, hm⟩ := hw.1 i
  rw [hm]
  positivity

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)

local notation "I" => inst n k hk hkn w hw

include hk hkn hw

lemma delta_eq : (I).delta = delta k := rfl

lemma L_eq : (I).L = logFactor k := rfl

lemma valid : (I).Valid := (I).valid

lemma path_eq (x : Fin n → ℝ) (p : Fin n) :
    path k w x p = PagingWithDelay.PMD.mdPath I x p := by
  funext s i
  simp [path, PagingWithDelay.PMD.mdPath, PagingWithDelay.PMD.evictCurve,
    PagingWithDelay.PMD.restMass, inst]

lemma isRest_iff (x : Fin n → ℝ) : PagingWithDelay.PMD.IsRest I x ↔ StateValid k x := by
  simp [PagingWithDelay.PMD.IsRest, PagingWithDelay.PMD.IsFrac, StateValid,
    PagingWithDelay.PMD.restMass, inst, PagingWithDelay.Instance.delta, delta]

lemma pathLength_eq {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n) :
    pathLength k w x p = PagingWithDelay.PMD.serviceEnd I x p := by
  have hxr := (isRest_iff hk hkn hw x).2 hx
  have hv := valid hk hkn hw
  have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ path k w x p s p = delta k} := ⟨0, fun s hs => hs.1⟩
  rcases eq_or_lt_of_le (hx.1 p).1 with h | h
  · -- `x_p = δ`: both are `0`
    have h0 : PagingWithDelay.PMD.serviceEnd I x p = 0 :=
      PagingWithDelay.PMD.serviceEnd_eq_zero_of_le hxr (le_of_eq h.symm)
    have hmem : (0 : ℝ) ∈ {s : ℝ | 0 ≤ s ∧ path k w x p s p = delta k} := by
      refine ⟨le_rfl, ?_⟩
      rw [path_eq hk hkn hw, PagingWithDelay.PMD.mdPath_zero_self' hxr]
      exact h.symm
    unfold pathLength
    rw [if_pos ⟨0, hmem⟩, h0]
    exact le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨0, hmem⟩ fun s hs => hs.1)
  · -- `δ < x_p`
    have hS0 := PagingWithDelay.PMD.serviceEnd_nonneg hv hxr h
    have hmem : PagingWithDelay.PMD.serviceEnd I x p ∈
        {s : ℝ | 0 ≤ s ∧ path k w x p s p = delta k} := by
      refine ⟨hS0, ?_⟩
      rw [path_eq hk hkn hw]
      exact PagingWithDelay.PMD.mdPath_serviceEnd hv hxr h
    unfold pathLength
    rw [if_pos ⟨_, hmem⟩]
    refine le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨_, hmem⟩ fun s hs => ?_)
    apply PagingWithDelay.PMD.serviceEnd_le_of_mem hs.1
    rw [← path_eq hk hkn hw]
    exact hs.2.le

lemma pathEnd_eq {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n) :
    pathEnd k w x p = PagingWithDelay.PMD.criticalState I x p := by
  unfold pathEnd PagingWithDelay.PMD.criticalState
  rw [pathLength_eq hk hkn hw hx, path_eq hk hkn hw]

lemma stateValid_pathEnd {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n) :
    StateValid k (pathEnd k w x p) := by
  rw [pathEnd_eq hk hkn hw hx, ← isRest_iff hk hkn hw]
  exact PagingWithDelay.PMD.criticalState_isRest' (valid hk hkn hw)
    ((isRest_iff hk hkn hw x).2 hx) p

end

/-- **Lemma 10** (`lem:drop`, `serviceEnd_le_add_serviceEnd`). -/
theorem lemma10 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p q : Fin n) (hp : delta k < x p) (hpq : q ≠ p) (hq : delta k < x q) :
    pathLength k w x q ≤ pathLength k w x p + pathLength k w (pathEnd k w x p) q := by
  have hw' := weight_pos_of_PMDWeights hw
  rw [pathLength_eq hk hkn hw' hx, pathLength_eq hk hkn hw' hx,
    pathLength_eq hk hkn hw' (stateValid_pathEnd hk hkn hw' hx p), pathEnd_eq hk hkn hw' hx]
  exact PagingWithDelay.PMD.serviceEnd_le_add_serviceEnd (valid hk hkn hw')
    ((isRest_iff hk hkn hw' x).2 hx) (Ne.symm hpq) hq

end PagingDelay.PMD.Bridge
end

/-! ## Inlined from `PagingWithDelay.Trigger` -/
section

/-!
# The trigger: delays, overshoots, trigger times, and claims

* `pageDelay pending p` and the overshoots are continuous in `t` when the delay functions of the pending requests are. Hence a page critical at `t` satisfies the closed form `Triggered` of the trigger at `t`: `delay_p(t) ≥ c_p + w_p` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)|/L`. The analysis only uses `Triggered`.
* Some page is critical at the infimum of `triggerTimes s` (finitely many pages), so an advance is followed by a critical service; if no page is critical now, the infimum is strictly later.
* A pending request with an unbounded monotone delay function makes `triggerTimes s` nonempty.
* Facts about `triggerPage`.
* The claims update `claimUpdate`: only the pages `q` with `w_q ≤ w_p` change, each `c_q` by the same fraction `θ ≤ 1` of `o_q`; the total increase is `min (|λ_p(x)|/L) (∑_{q : w_q ≤ w_p} o_q)`, which is `|λ_p(x)|/L` when `p` satisfies `Triggered`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (serviceEnd)

noncomputable section

variable {input : Instance Page}

/-! ### Page delays -/

@[simp] theorem pageDelay_nil (p : Page) (t : ℝ) :
    pageDelay ([] : List (Request Page)) p t = 0 := by
  simp [pageDelay]

theorem continuous_pageDelay {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (p : Page) :
    Continuous (pageDelay pending p) := by
  unfold pageDelay
  refine continuous_list_sum (f := fun (ρ : Request Page) (t : ℝ) => ρ.delay (t - ρ.arrival)) _ ?_
  intro ρ hρ
  exact (hc ρ (List.mem_filter.mp hρ).1).comp (continuous_id.sub continuous_const)

theorem continuous_overshoot {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (p : Page) :
    Continuous (overshoot input pending claims p) := by
  unfold overshoot
  exact continuous_const.max
    (((continuous_pageDelay hc p).sub continuous_const).sub continuous_const)

theorem continuous_sum_overshoot {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (S : Finset Page) :
    Continuous (fun t => ∑ q ∈ S, overshoot input pending claims q t) :=
  continuous_finset_sum _ fun q _ => continuous_overshoot hc claims q

theorem overshoot_nonneg (pending : List (Request Page)) (claims : Page → ℝ) (p : Page)
    (t : ℝ) : 0 ≤ overshoot input pending claims p t :=
  le_max_left _ _

theorem overshoot_pos_iff {pending : List (Request Page)} {claims : Page → ℝ} {p : Page}
    {t : ℝ} :
    0 < overshoot input pending claims p t ↔ claims p + w p < pageDelay pending p t := by
  unfold overshoot
  constructor
  · intro h
    rcases le_total 0 (pageDelay pending p t - claims p - w p) with h1 | h1
    · rw [max_eq_right h1] at h; linarith
    · rw [max_eq_left h1] at h; exact absurd h (lt_irrefl 0)
  · intro h
    exact lt_max_of_lt_right (by linarith)

theorem le_overshoot (pending : List (Request Page)) (claims : Page → ℝ) (p : Page) (t : ℝ) :
    pageDelay pending p t - claims p - w p ≤ overshoot input pending claims p t :=
  le_max_right _ _

/-- A nonzero page delay needs a pending request on the page. -/
theorem exists_pending_of_pageDelay_ne {pending : List (Request Page)} {p : Page} {t : ℝ}
    (h : pageDelay pending p t ≠ 0) : ∃ ρ ∈ pending, ρ.page = p := by
  by_contra hno
  push_neg at hno
  apply h
  unfold pageDelay
  rw [List.filter_eq_nil_iff.mpr (by intro ρ hρ; simpa using hno ρ hρ)]
  simp

/-- The delay of one pending request on `p` is at most the page delay. -/
theorem delay_le_pageDelay {pending : List (Request Page)} {t : ℝ}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ pending, ρ.delay 0 = 0)
    (harr : ∀ ρ ∈ pending, ρ.arrival ≤ t) {ρ : Request Page} (hρ : ρ ∈ pending) :
    ρ.delay (t - ρ.arrival) ≤ pageDelay pending ρ.page t := by
  unfold pageDelay
  apply List.single_le_sum
  · intro v hv
    simp only [List.mem_map, List.mem_filter] at hv
    obtain ⟨π, ⟨hπ, -⟩, rfl⟩ := hv
    rw [← hzero π hπ]
    exact hmono π hπ (by linarith [harr π hπ])
  · exact List.mem_map.mpr ⟨ρ, List.mem_filter.mpr ⟨hρ, by simp⟩, rfl⟩

theorem pageDelay_mono {pending : List (Request Page)} (hmono : ∀ ρ ∈ pending, Monotone ρ.delay)
    (p : Page) : Monotone (pageDelay pending p) := by
  intro a b hab
  unfold pageDelay
  apply List.sum_le_sum
  intro ρ hρ
  exact hmono ρ (List.mem_filter.mp hρ).1 (by linarith)

/-- The page delay only depends on the pending requests on the page. -/
theorem pageDelay_filter_ne (pending : List (Request Page)) {p q : Page} (hpq : q ≠ p) (t : ℝ) :
    pageDelay (pending.filter fun π => decide (π.page ≠ p)) q t = pageDelay pending q t := by
  unfold pageDelay
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro ρ _
  by_cases h : ρ.page = q
  · subst h; simp [hpq]
  · simp [h]

/-! ### Triggering -/

variable (input) in
/-- The closed form of the trigger at `t`: `delay_p(t) ≥ c_p + w_p` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L`. It holds whenever `eq:trigger` holds (`triggered_of_triggerCond`) and, by continuity, whenever `p` is critical at `t` (`triggered_of_critical`). -/
def Triggered (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  claims p + w p ≤ pageDelay pending p t ∧
    serviceEnd input x p / L ≤
      ∑ q ∈ lighter input p, overshoot input pending claims q t

theorem triggered_iff {x : Page → ℝ} {pending : List (Request Page)} {claims : Page → ℝ}
    {t : ℝ} {p : Page} :
    Triggered input x pending claims t p ↔
      claims p + w p ≤ pageDelay pending p t ∧
        serviceEnd input x p / L ≤
          ∑ q ∈ lighter input p, overshoot input pending claims q t := Iff.rfl

theorem triggerCond_iff {x : Page → ℝ} {pending : List (Request Page)} {claims : Page → ℝ}
    {t : ℝ} {p : Page} :
    TriggerCond input x pending claims t p ↔
      claims p + w p < pageDelay pending p t ∧
        serviceEnd input x p / L ≤
          ∑ q ∈ lighter input p, overshoot input pending claims q t := by
  rw [TriggerCond, overshoot_pos_iff]

theorem triggered_of_triggerCond {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : TriggerCond input x pending claims t p) :
    Triggered input x pending claims t p :=
  ⟨(triggerCond_iff.mp h).1.le, h.2⟩

theorem mem_lighter {p q : Page} : q ∈ lighter input p ↔ w q ≤ w p := by
  simp [lighter]

theorem self_mem_lighter (p : Page) : p ∈ lighter input p := mem_lighter.mpr le_rfl

/-- A triggered page has a pending request (claims are nonnegative and weights positive). -/
theorem exists_pending_of_triggered {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : Triggered input x pending claims t p)
    (hc : 0 ≤ claims p) (hw : 0 < w p) : ∃ ρ ∈ pending, ρ.page = p := by
  apply exists_pending_of_pageDelay_ne (t := t)
  have := h.1
  intro h0
  linarith

/-- A critical page has a pending request: `eq:trigger` holds at some time, so its page delay is positive. -/
theorem exists_pending_of_critical {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : Critical input x pending claims t p)
    (hc : 0 ≤ claims p) (hw : 0 < w p) : ∃ ρ ∈ pending, ρ.page = p := by
  obtain ⟨τ, -, -, hτ⟩ := h 1 one_pos
  exact exists_pending_of_triggered (triggered_of_triggerCond hτ) hc hw

theorem isClosed_triggered {x : Page → ℝ} {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (p : Page) :
    IsClosed {t | Triggered input x pending claims t p} := by
  simp only [triggered_iff, Set.setOf_and]
  exact (isClosed_le continuous_const (continuous_pageDelay hc p)).inter
    (isClosed_le continuous_const (continuous_sum_overshoot hc claims _))

/-- A page that is critical at `t` satisfies the closed form of the trigger at `t`: `t` is a limit of times at which `eq:trigger` holds. -/
theorem triggered_of_critical {x : Page → ℝ} {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) {claims : Page → ℝ} {t : ℝ} {p : Page}
    (h : Critical input x pending claims t p) : Triggered input x pending claims t p := by
  have hsub : {τ | TriggerCond input x pending claims τ p} ⊆
      {τ | Triggered input x pending claims τ p} := fun τ hτ => triggered_of_triggerCond hτ
  have hcl : t ∈ closure {τ | TriggerCond input x pending claims τ p} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨τ, h1, h2, h3⟩ := h ε hε
    refine ⟨τ, h3, ?_⟩
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  exact closure_minimal hsub (isClosed_triggered hc claims p) hcl

theorem triggerTimes_bddBelow (s : Snap Page) : BddBelow (triggerTimes input s) :=
  ⟨s.now, fun _ ht => ht.1⟩

theorem now_le_sInf_triggerTimes {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    s.now ≤ sInf (triggerTimes input s) :=
  le_csInf hne fun _ ht => ht.1

theorem sInf_triggerTimes_le {s : Snap Page} {t : ℝ} (ht : t ∈ triggerTimes input s) :
    sInf (triggerTimes input s) ≤ t :=
  csInf_le (triggerTimes_bddBelow s) ht

/-- Some page is critical at the infimum of the trigger times: as there are finitely many pages, `eq:trigger` holds for one of them arbitrarily soon after the infimum. -/
theorem exists_critical_sInf {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    ∃ p, Critical input s.x s.pending s.claims (sInf (triggerTimes input s)) p := by
  by_contra hno
  push_neg at hno
  have hno' : ∀ p, ∃ ε > 0, ∀ τ, sInf (triggerTimes input s) ≤ τ →
      τ < sInf (triggerTimes input s) + ε →
        ¬ TriggerCond input s.x s.pending s.claims τ p := by
    intro p
    have := hno p
    unfold Critical at this
    push_neg at this
    exact this
  choose ε hε hε' using hno'
  obtain ⟨t0, -, p0, -⟩ := id hne
  set η := Finset.univ.inf' ⟨p0, Finset.mem_univ p0⟩ ε with hηdef
  have hη : 0 < η := (Finset.lt_inf'_iff _).2 fun p _ => hε p
  obtain ⟨t, htT, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (triggerTimes input s)) hη)
  obtain ⟨p, hp⟩ := htT.2
  have hle : η ≤ ε p := Finset.inf'_le ε (Finset.mem_univ p)
  exact hε' p t (sInf_triggerTimes_le htT) (by linarith) hp

theorem triggerPage_spec {s : Snap Page} {p : Page} (h : triggerPage input s = some p) :
    Critical input s.x s.pending s.claims s.now p := by
  have := List.find?_some h
  simpa using this

/-- The page of the next critical service satisfies the closed form of the trigger now. -/
theorem triggerPage_triggered {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    {p : Page} (h : triggerPage input s = some p) :
    Triggered input s.x s.pending s.claims s.now p :=
  triggered_of_critical hc (triggerPage_spec h)

theorem triggerPage_eq_none_iff {s : Snap Page} :
    triggerPage input s = none ↔ ∀ p, ¬ Critical input s.x s.pending s.claims s.now p := by
  unfold triggerPage
  rw [List.find?_eq_none]
  constructor
  · intro h p hp
    exact h p (by simp) (by simpa using hp)
  · intro h p _ hp
    exact h p (by simpa using hp)

theorem triggerPage_eq_some_of_critical {s : Snap Page} {p : Page}
    (h : Critical input s.x s.pending s.claims s.now p) : ∃ q, triggerPage input s = some q := by
  cases hq : triggerPage input s with
  | none => exact absurd h (triggerPage_eq_none_iff.mp hq p)
  | some q => exact ⟨q, rfl⟩

/-- Without a page critical now, the infimum of the trigger times is strictly later. -/
theorem now_lt_sInf_triggerTimes {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    (hne : (triggerTimes input s).Nonempty) (hnone : triggerPage input s = none) :
    s.now < sInf (triggerTimes input s) := by
  rcases eq_or_lt_of_le (now_le_sInf_triggerTimes hne) with h | h
  · obtain ⟨p, hp⟩ := exists_critical_sInf hne
    rw [← h] at hp
    exact absurd hp (triggerPage_eq_none_iff.mp hnone p)
  · exact h

/-- After advancing to the infimum of the trigger times, some page is critical. -/
theorem triggerPage_advance {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    (hne : (triggerTimes input s).Nonempty) :
    ∃ p, triggerPage input { s with now := sInf (triggerTimes input s) } = some p := by
  obtain ⟨p, hp⟩ := exists_critical_sInf hne
  exact triggerPage_eq_some_of_critical (s := { s with now := sInf (triggerTimes input s) }) hp

/-- A pending request with an unbounded monotone delay function eventually makes `eq:trigger` hold for its page. -/
theorem triggerTimes_nonempty {s : Snap Page}
    (hmono : ∀ ρ ∈ s.pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ s.pending, ρ.delay 0 = 0)
    (hunb : ∀ ρ ∈ s.pending, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ)
    (harr : ∀ ρ ∈ s.pending, ρ.arrival ≤ s.now) {ρ : Request Page} (hρ : ρ ∈ s.pending) :
    (triggerTimes input s).Nonempty := by
  set p := ρ.page
  set thr := serviceEnd input s.x p / L
  obtain ⟨τ, hτ⟩ := hunb ρ hρ (s.claims p + w p + |thr| + 1)
  set t := max s.now (ρ.arrival + τ)
  have harr' : ∀ π ∈ s.pending, π.arrival ≤ t := fun π hπ => (harr π hπ).trans (le_max_left _ _)
  have h1 : ρ.delay τ ≤ ρ.delay (t - ρ.arrival) :=
    hmono ρ hρ (by have := le_max_right s.now (ρ.arrival + τ); linarith)
  have h2 := delay_le_pageDelay hmono hzero harr' hρ
  refine ⟨t, le_max_left _ _, p, triggerCond_iff.mpr ⟨?_, ?_⟩⟩
  · linarith [abs_nonneg thr]
  · calc thr ≤ |thr| := le_abs_self _
      _ ≤ pageDelay s.pending p t - s.claims p - w p := by linarith
      _ ≤ overshoot input s.pending s.claims p t := le_overshoot _ _ _ _
      _ ≤ _ := Finset.single_le_sum (f := fun q => overshoot input s.pending s.claims q t)
          (fun q _ => overshoot_nonneg _ _ _ _) (self_mem_lighter (input := input) p)

/-- The same, for the pending requests of a valid instance. -/
theorem triggerTimes_nonempty_of_valid (hv : input.Valid) {s : Snap Page}
    (hreq : ∀ ρ ∈ s.pending, ρ ∈ input.requests) (harr : ∀ ρ ∈ s.pending, ρ.arrival ≤ s.now)
    {ρ : Request Page} (hρ : ρ ∈ s.pending) : (triggerTimes input s).Nonempty :=
  triggerTimes_nonempty (fun π hπ => hv.delay_mono π (hreq π hπ))
    (fun π hπ => hv.delay_zero π (hreq π hπ)) (fun π hπ => hv.delay_unbounded π (hreq π hπ))
    harr hρ

/-- If `eq:trigger` does not hold for page `p` at any time in `[a, t)` (with `a < t`) and `p` has positive overshoot at `t`, then at `t` the overshoots of the lighter pages are at most `|λ_p(x)|/L`. -/
theorem sum_overshoot_le_of_not_triggered {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} (hc : ∀ ρ ∈ pending, Continuous ρ.delay) {a t : ℝ} (hat : a < t)
    {p : Page} (hno : ∀ τ, a ≤ τ → τ < t → ¬ TriggerCond input x pending claims τ p)
    (hpos : claims p + w p < pageDelay pending p t) :
    ∑ q ∈ lighter input p, overshoot input pending claims q t ≤
      serviceEnd input x p / L := by
  by_contra hlt
  push_neg at hlt
  set U := {τ | claims p + w p < pageDelay pending p τ} ∩
    {τ | serviceEnd input x p / L <
      ∑ q ∈ lighter input p, overshoot input pending claims q τ}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (continuous_pageDelay hc p)).inter
      (isOpen_lt continuous_const (continuous_sum_overshoot hc claims _))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t ⟨hpos, hlt⟩
  set τ := max a (t - ε / 2)
  have hτ1 : a ≤ τ := le_max_left _ _
  have hτ2 : τ < t := max_lt hat (by linarith)
  have hτ3 : τ ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    have := le_max_right a (t - ε / 2)
    linarith
  have hτU := hball hτ3
  exact hno τ hτ1 hτ2 (triggerCond_iff.mpr ⟨hτU.1, hτU.2.le⟩)

/-! ### Claims -/

/-! ### The claims of a critical service -/

theorem serviceEnd_nonneg' (x : Page → ℝ) (p : Page) : 0 ≤ serviceEnd input x p :=
  Real.sInf_nonneg fun _ hs => hs.1

theorem claimRem_nonneg (hv : input.Valid) (x : Page → ℝ) (p : Page) :
    0 ≤ serviceEnd input x p / L :=
  div_nonneg (serviceEnd_nonneg' x p) (Instance.L_pos hv).le

theorem claimFraction_nonneg (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    0 ≤ claimFraction input x pending claims t p :=
  le_min zero_le_one (div_nonneg (claimRem_nonneg hv x p)
    (Finset.sum_nonneg fun q _ => overshoot_nonneg _ _ _ _))

theorem claimFraction_le_one (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    claimFraction input x pending claims t p ≤ 1 :=
  min_le_left _ _

theorem le_claimUpdate (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p q : Page) :
    claims q ≤ claimUpdate input x pending claims t p q := by
  unfold claimUpdate
  split_ifs
  · nlinarith [claimFraction_nonneg hv x pending claims t p, overshoot_nonneg (input := input) pending claims q t]
  · exact le_rfl

theorem claimUpdate_le (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p q : Page) :
    claimUpdate input x pending claims t p q ≤ claims q + overshoot input pending claims q t := by
  unfold claimUpdate
  split_ifs
  · nlinarith [claimFraction_le_one (input := input) x pending claims t p,
      overshoot_nonneg (input := input) pending claims q t]
  · linarith [overshoot_nonneg (input := input) pending claims q t]

/-- Only the pages `q` with `w_q ≤ w_p` give claims. -/
theorem claimUpdate_of_not_lighter (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) {p q : Page} (hq : q ∉ lighter input p) :
    claimUpdate input x pending claims t p q = claims q :=
  if_neg hq

/-- The total claim of a critical service on `p`: `min (|λ_p(x)|/L) (∑_{q : w_q ≤ w_p} o_q)`. -/
theorem sum_claimUpdate (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      min (serviceEnd input x p / L)
        (∑ q ∈ lighter input p, overshoot input pending claims q t) := by
  set S := ∑ q ∈ lighter input p, overshoot input pending claims q t
  have hS : 0 ≤ S := Finset.sum_nonneg fun q _ => overshoot_nonneg _ _ _ _
  have hsum : ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      claimFraction input x pending claims t p * S := by
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ (lighter input p))
      (fun q _ hq => by rw [claimUpdate_of_not_lighter x pending claims t hq, sub_self])]
    exact Finset.sum_congr rfl fun q hq => by simp [claimUpdate, hq]
  rw [hsum]
  rcases hS.eq_or_lt with h | h
  · rw [← h, mul_zero, min_eq_right (claimRem_nonneg hv x p)]
  · unfold claimFraction
    rw [min_mul_of_nonneg _ _ hS, one_mul, div_mul_cancel₀ _ h.ne', min_comm]

/-- When `p` triggers, the claims of the critical service total exactly `|λ_p(x)|/L`. -/
theorem sum_claimUpdate_of_triggered (hv : input.Valid) {x : Page → ℝ}
    {pending : List (Request Page)} {claims : Page → ℝ} {t : ℝ} {p : Page}
    (h : Triggered input x pending claims t p) :
    ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      serviceEnd input x p / L := by
  rw [sum_claimUpdate hv, min_eq_left h.2]

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Hole` -/
section

/-!
# The hole of a preemptive service

The hole raises only pages of weight `≤ 2^e`, each by the same fraction of its cached mass, stays below `1`, and — if these pages hold cached mass at least `1 - δ` — raises by exactly `1 - δ`, so its closing cost is at most `(1 - δ) 2^e`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

variable (input) in
/-- The closing cost `∑ᵢ wᵢ (x^hole_i - x_i)`: the fetch cost of closing the hole opened from `x`, at most the payment `W (1 - δ)` (`closingCost_le`). -/
noncomputable def closingCost (x : Page → ℝ) (e : ℤ) : ℝ :=
  ∑ i, w i * (hole input x e i - x i)

/-! ### The hole -/

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x) (e : ℤ)
include hv hx

/-- The cached mass `∑_{i : w_i ≤ W} (1 - x_i)` of the pages a level-`W` hole raises is nonnegative. -/
theorem lightMass_nonneg :
    0 ≤ ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i) :=
  Finset.sum_nonneg fun i _ => by linarith [(hx i).2]

theorem holeFraction_nonneg : 0 ≤ holeFraction input x e :=
  le_min zero_le_one
    (div_nonneg (by linarith [delta_lt_one hv]) (lightMass_nonneg hv hx e))

theorem holeFraction_le_one : holeFraction input x e ≤ 1 := min_le_left _ _

theorem hole_bounds : (∀ i, x i ≤ hole input x e i) ∧ (∀ i, hole input x e i ≤ 1) := by
  have h0 := holeFraction_nonneg hv hx e
  have h1 := holeFraction_le_one hv hx e
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> unfold hole <;> split_ifs
  · nlinarith [(hx i).2]
  · exact le_rfl
  · nlinarith [(hx i).2]
  · exact (hx i).2

theorem le_hole (i : Page) : x i ≤ hole input x e i := (hole_bounds hv hx e).1 i

theorem hole_le_one (i : Page) : hole input x e i ≤ 1 := (hole_bounds hv hx e).2 i

theorem hole_isFrac : IsFrac input (hole input x e) := fun i =>
  ⟨(hx i).1.trans (le_hole hv hx e i), hole_le_one hv hx e i⟩

theorem hole_eq_of_lt_level {i : Page} (hi : e < level input i) : hole input x e i = x i :=
  if_neg (by omega)

/-- The hole raises the pages of weight `≤ W` by `min (1 - δ) (∑_{i : w_i ≤ W} (1 - x_i))` in total. -/
theorem hole_sum :
    ∑ i, hole input x e i = ∑ i, x i +
      min (1 - δ) (∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) := by
  set S := ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)
  have hS : 0 ≤ S := lightMass_nonneg hv hx e
  have hδ : 0 < 1 - δ := by linarith [delta_lt_one hv]
  have hraise : ∑ i, (hole input x e i - x i) = holeFraction input x e * S := by
    rw [Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by unfold hole; split_ifs <;> ring
  have hθ : holeFraction input x e * S = min (1 - δ) S := by
    rcases hS.eq_or_lt with h | h
    · rw [← h, mul_zero, min_eq_right hδ.le]
    · unfold holeFraction
      rw [min_mul_of_nonneg _ _ hS, one_mul, div_mul_cancel₀ _ h.ne', min_comm]
  linarith [Finset.sum_sub_distrib (s := Finset.univ) (f := hole input x e) (g := x)]

theorem closingCost_le : closingCost input x e ≤ (1 - δ) * levelWeight e := by
  have h1 : closingCost input x e ≤ ∑ i, levelWeight e * (hole input x e i - x i) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : level input i ≤ e
    · apply mul_le_mul_of_nonneg_right ((level_le_iff hv i e).mp hi)
      linarith [le_hole hv hx e i]
    · rw [hole_eq_of_lt_level hv hx e (by omega)]; simp
  have h2 : ∑ i, (hole input x e i - x i) ≤ 1 - δ := by
    rw [Finset.sum_sub_distrib, hole_sum hv hx e]
    linarith [min_le_left (1 - δ)
      (∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i))]
  rw [← Finset.mul_sum] at h1
  nlinarith [levelWeight_pos e]

/-- Opening the hole fetches nothing. -/
theorem hole_fetch_open :
    ∑ i, w i * max 0 (x i - hole input x e i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [max_eq_left (by linarith [le_hole hv hx e i]), mul_zero]

/-- Closing the hole fetches exactly the closing cost. -/
theorem hole_fetch_close :
    ∑ i, w i * max 0 (hole input x e i - x i) = closingCost input x e := by
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_right (by linarith [le_hole hv hx e i])]

/-- Under the second preemptive service condition the hole has total size exactly `1 - δ`. -/
theorem sum_hole (hcond : 1 - δ ≤
      ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) :
    ∑ i, hole input x e i = ∑ i, x i + (1 - δ) := by
  rw [hole_sum hv hx e, min_eq_left hcond]

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Step` -/
section

/-!
# One move of the loop

Characterization of `next` by its move.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage)

noncomputable section

variable {input : Instance Page}

/-- The condition under which an idle loop advances to the infimum of the trigger times. -/
def AdvanceCond (input : Instance Page) (s : Snap Page) : Prop :=
  (triggerTimes input s).Nonempty ∧ ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a

theorem next_tick {s s' : Snap Page} {t : ℝ} (h : next input s = some (.tick t, s')) :
    s.stage = .idle ∧ triggerPage input s = none ∧ ¬ AdvanceCond input s ∧
    s.upcoming = t :: s.upcoming.tail ∧
    s' = { s with
      now := t
      upcoming := s.upcoming.tail
      pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
        fun ρ => decide (s.x ρ.page ≠ δ) } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      · simp at h
      · split at h
        · simp at h
        · rename_i t' rest
          simp only [Option.some.injEq, Prod.mk.injEq, Move.tick.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, hf, hc, rfl, rfl⟩
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_advance {s s' : Snap Page} {t : ℝ} (h : next input s = some (.advance t, s')) :
    s.stage = .idle ∧ triggerPage input s = none ∧ AdvanceCond input s ∧
    t = sInf (triggerTimes input s) ∧
    s' = { s with now := t } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.advance.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hf, hc, rfl, rfl⟩
      · split at h
        · simp at h
        · simp at h
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_critical {s s' : Snap Page} {p : Page}
    (h : next input s = some (.critical p, s')) :
    s.stage = .idle ∧ triggerPage input s = some p ∧
    s' = { s with
      x := criticalState input s.x p
      budget := deposit input s.x p s.budget
      pending := s.pending.filter fun π => decide (π.page ≠ p)
      claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
      stage := .examine (minLevel input) } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · rename_i p' hf
      simp only [Option.some.injEq, Prod.mk.injEq, Move.critical.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hf, rfl⟩
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_skip {s s' : Snap Page} {e : ℤ} (h : next input s = some (.skip e, s')) :
    s.stage = .examine e ∧ ¬ preemptCondition input s.x s.budget e ∧
    s' = { s with stage := afterLevel input e } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h with hb
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq, Move.skip.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hb, rfl⟩
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_openHole {s s' : Snap Page} {e : ℤ} (h : next input s = some (.openHole e, s')) :
    s.stage = .examine e ∧ preemptCondition input s.x s.budget e ∧
    s' = { s with
      x := hole input s.x e
      budget := Function.update s.budget e (s.budget e - holePayment input e)
      stage := .preempt e s.x } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq, Prod.mk.injEq, Move.openHole.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hb, rfl⟩
    · simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_trip {s s' : Snap Page} {e : ℤ} {π : Request Page}
    (h : next input s = some (.trip e π, s')) :
    (∃ b, s.stage = .preempt e b) ∧
    tripCandidate input s.pending s.now e = some π ∧
    levelWeight e ≤ s.budget e ∧
    s' = { s with
      budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
      pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
      claims := Function.update s.claims π.page 0 } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i π' hπ
      split_ifs at h with hcost
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.trip.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨⟨b, rfl⟩, hπ, hcost, rfl⟩
      · simp at h

theorem next_closeHole {s s' : Snap Page} {e : ℤ} {stop : Option (Request Page)}
    (h : next input s = some (.closeHole e stop, s')) :
    ∃ b, s.stage = .preempt e b ∧
    (match stop with
      | none => tripCandidate input s.pending s.now e = none
      | some π => tripCandidate input s.pending s.now e = some π ∧
          s.budget e < levelWeight e) ∧
    s' = { s with x := b, stage := afterLevel input e } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · rename_i hπ
      simp only [Option.some.injEq, Prod.mk.injEq, Move.closeHole.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨b, rfl, hπ, rfl⟩
    · rename_i π' hπ
      split_ifs at h with hcost
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.closeHole.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨b, rfl, ⟨hπ, lt_of_not_ge hcost⟩, rfl⟩

/-- `next` is `none` exactly at an idle state where no page triggers, no trigger time is left, and no arrival time is left. -/
theorem next_eq_none {s : Snap Page} (h : next input s = none) :
    s.stage = .idle ∧ triggerPage input s = none ∧ ¬ (triggerTimes input s).Nonempty ∧
      s.upcoming = [] := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      cases up with
      | nil =>
        refine ⟨rfl, hf, ?_, rfl⟩
        intro hne
        apply hc
        refine ⟨hne, ?_⟩
        simp
      | cons t rest => simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Invariant` -/
section

/-!
# The run of the loop: generic chain facts, the invariant, and termination

* `runSnap n s i` is the state before entry `i` of `run n s` (the final state once `i` is past the end); consecutive states are related by `next`.
* `Inv` is the invariant of the loop (`lem:inv`) and `Started` says that the current time lies strictly before all upcoming arrival times (true after the first move).
* `measure` strictly decreases along `next`, which gives termination within `fuel` moves.
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage IsRest IsFrac
  restMass)

noncomputable section

variable (input : Instance Page)

/-! ### Generic facts about `run` -/

/-- The state before entry `i` of `run n s`. -/
def runSnap (n : ℕ) (s : Snap Page) (i : ℕ) : Snap Page :=
  if h : i < (run input n s).1.length then ((run input n s).1[i]).1 else (run input n s).2

variable {input}

theorem run_succ_of_next {n : ℕ} {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) :
    run input (n + 1) s = ((s, m) :: (run input n s').1, (run input n s').2) := by
  simp [run, h]

theorem run_succ_of_none {n : ℕ} {s : Snap Page} (h : next input s = none) :
    run input (n + 1) s = ([], s) := by
  simp [run, h]

theorem runSnap_zero (n : ℕ) (s : Snap Page) : runSnap input n s 0 = s := by
  cases n with
  | zero => simp [runSnap, run]
  | succ n =>
    cases h : next input s with
    | none => simp [runSnap, run_succ_of_none h]
    | some p =>
      obtain ⟨m, s'⟩ := p
      simp [runSnap, run_succ_of_next h]

theorem runSnap_succ_of_next {n : ℕ} {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) (i : ℕ) :
    runSnap input (n + 1) s (i + 1) = runSnap input n s' i := by
  simp [runSnap, run_succ_of_next h]

theorem next_runSnap : ∀ (n : ℕ) (s : Snap Page) (i : ℕ) (hi : i < (run input n s).1.length),
    next input (runSnap input n s i) =
      some (((run input n s).1[i]).2, runSnap input n s (i + 1)) := by
  intro n
  induction n with
  | zero => intro s i hi; simp [run] at hi
  | succ n ih =>
    intro s i hi
    cases h : next input s with
    | none => simp [run_succ_of_none h] at hi
    | some p =>
      obtain ⟨m, s'⟩ := p
      cases i with
      | zero =>
        rw [runSnap_zero, runSnap_succ_of_next h, runSnap_zero, h]
        simp [run_succ_of_next h]
      | succ i =>
        have hi' : i < (run input n s').1.length := by
          simpa [run_succ_of_next h] using hi
        rw [runSnap_succ_of_next h, runSnap_succ_of_next h, ih s' i hi']
        simp [run_succ_of_next h]

theorem next_run_final (μ : Snap Page → ℕ) (P : Snap Page → Prop)
    (hstep : ∀ s m s', P s → next input s = some (m, s') → P s' ∧ μ s' < μ s) :
    ∀ (n : ℕ) (s : Snap Page), P s → μ s < n → next input (run input n s).2 = none := by
  intro n
  induction n with
  | zero => intro s _ h; omega
  | succ n ih =>
    intro s hs hμ
    cases h : next input s with
    | none => simpa [run_succ_of_none h] using h
    | some p =>
      obtain ⟨m, s'⟩ := p
      obtain ⟨hs', hμ'⟩ := hstep s m s' hs h
      rw [run_succ_of_next h]
      exact ih s' hs' (by omega)

/-! ### Arrival times -/

theorem arrivalTimes_pairwise : (arrivalTimes input).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort ((input.requests.map Request.arrival).toFinset) (· ≤ ·)
  have h2 := Finset.sort_nodup ((input.requests.map Request.arrival).toFinset) (· ≤ ·)
  exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2

theorem arrival_mem_arrivalTimes {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ρ.arrival ∈ arrivalTimes input := by
  unfold arrivalTimes
  rw [Finset.mem_sort, List.mem_toFinset]
  exact List.mem_map_of_mem hρ

theorem arrivalTimes_length_le : (arrivalTimes input).length ≤ input.requests.length := by
  unfold arrivalTimes
  rw [Finset.length_sort]
  exact (List.toFinset_card_le _).trans (by simp)

/-! ### The invariant -/

/-- The state outside the current preemptive service (same as `baseState`). -/
def baseOf (s : Snap Page) : Page → ℝ :=
  match s.stage with
  | .preempt _ base => base
  | _ => s.x

theorem baseOf_congr {s s' : Snap Page} (h1 : s'.stage = s.stage) (h2 : s'.x = s.x) :
    baseOf s' = baseOf s := by
  unfold baseOf; rw [h1, h2]

theorem baseOf_of_not_preempt {s : Snap Page} (hs : ∀ e b, s.stage ≠ .preempt e b) :
    baseOf s = s.x := by
  unfold baseOf
  split
  · rename_i e b h; exact absurd h (hs e b)
  · rfl

theorem afterLevel_ne_preempt (e e' : ℤ) (b : Page → ℝ) :
    afterLevel input e ≠ (.preempt e' b : Stage Page) := by
  unfold afterLevel; split_ifs <;> simp

/-- The current time lies strictly before all upcoming arrival times (true after the first move). -/
def Started (input : Instance Page) (s : Snap Page) : Prop :=
  ∀ a ∈ s.upcoming, s.now < a

/-- The invariant of the loop. -/
structure Inv (input : Instance Page) (s : Snap Page) : Prop where
  upc : ∃ pre, arrivalTimes input = pre ++ s.upcoming
  times : s = initialSnap input ∨ Started input s
  pend : ∀ ρ ∈ s.pending, ρ ∈ input.requests ∧ ρ.arrival ≤ s.now ∧ ρ.arrival ∉ s.upcoming
  pend_delta : ∀ ρ ∈ s.pending, δ < baseOf s ρ.page
  rest : IsRest input (baseOf s)
  preempt : ∀ e b, s.stage = .preempt e b → s.x = hole input b e ∧
    1 - δ ≤ ∑ j ∈ Finset.univ.filter (fun j => level input j ≤ e), (1 - b j)
  budget : ∀ e, 0 ≤ s.budget e
  claims : ∀ q, 0 ≤ s.claims q
  claims_pos : ∀ q, 0 < s.claims q → ∃ ρ ∈ s.pending, ρ.page = q

theorem inv_initial (hv : input.Valid) : Inv input (initialSnap input) where
  upc := ⟨[], rfl⟩
  times := Or.inl rfl
  pend := by simp [initialSnap]
  pend_delta := by simp [initialSnap]
  rest := by
    simpa [baseOf, initialSnap] using
      PagingWithDelay.PMD.initialState_isRest hv
  preempt := by simp [initialSnap]
  budget := by simp [initialSnap]
  claims := by simp [initialSnap]
  claims_pos := by simp [initialSnap]

theorem Inv.upcoming_pairwise {s : Snap Page} (hs : Inv input s) :
    s.upcoming.Pairwise (· < ·) := by
  obtain ⟨pre, hpre⟩ := hs.upc
  have hp := (arrivalTimes_pairwise (input := input))
  rw [hpre] at hp
  exact (List.pairwise_append.mp hp).2.1

theorem Inv.now_le_upcoming {s : Snap Page} (hs : Inv input s) {a : ℝ} (ha : a ∈ s.upcoming) :
    s.now ≤ a := by
  rcases hs.times with h0 | h
  · subst h0
    simp only [initialSnap] at ha ⊢
    have hp := (arrivalTimes_pairwise (input := input))
    cases hA : arrivalTimes input with
    | nil => rw [hA] at ha; simp at ha
    | cons a0 rest =>
      rw [hA] at ha hp
      simp only [List.headD_cons]
      rcases List.mem_cons.mp ha with h1 | h1
      · exact h1.ge
      · exact (List.rel_of_pairwise_cons hp h1).le
  · exact (h a ha).le

theorem Inv.initial_or {s : Snap Page} (hs : Inv input s)
    (hnot : s.stage ≠ .idle ∨ s.pending ≠ []) : Started input s := by
  rcases hs.times with h0 | h
  · subst h0; simp [initialSnap] at hnot
  · exact h

theorem Inv.continuous {s : Snap Page} (hv : input.Valid) (hs : Inv input s) :
    ∀ ρ ∈ s.pending, Continuous ρ.delay :=
  fun ρ hρ => hv.delay_continuous ρ (hs.pend ρ hρ).1

theorem countP_mem_cons (l : List (Request Page)) {t : ℝ} {rest : List ℝ} (ht : t ∉ rest) :
    l.countP (fun ρ => decide (ρ.arrival ∈ t :: rest)) =
      l.countP (fun ρ => decide (ρ.arrival ∈ rest)) +
        (l.filter fun ρ => decide (ρ.arrival = t)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.filter_cons, ih]
    by_cases h1 : a.arrival = t
    · have h2 : a.arrival ∉ rest := h1 ▸ ht
      have e1 : decide (a.arrival ∈ t :: rest) = true := by simp [h1]
      have e2 : decide (a.arrival ∈ rest) = false := by simp [h2]
      have e3 : decide (a.arrival = t) = true := by simp [h1]
      rw [e1, e2, e3]
      simp
      omega
    · have e1 : decide (a.arrival ∈ t :: rest) = decide (a.arrival ∈ rest) := by simp [h1]
      have e3 : decide (a.arrival = t) = false := by simp [h1]
      rw [e1, e3]
      simp only [Bool.false_eq_true, if_false]
      split_ifs <;> omega

/-! ### The measure -/

variable (input) in
/-- A rank of the state, decreasing within a level loop and from an idle state where no page triggers to one where some page does. -/
def rank (s : Snap Page) : ℕ :=
  match s.stage with
  | .idle => if (triggerPage input s).isSome then 0 else 1
  | .examine e => 2 * (maxLevel input - e).toNat + 3
  | .preempt e _ => 2 * (maxLevel input - e).toNat + 2

variable (input) in
/-- The termination measure. -/
def measure (s : Snap Page) : ℕ :=
  (s.upcoming.length + s.pending.length +
      input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming))) *
    (2 * numLevels input + 4) + rank input s

theorem rank_idle_le {s : Snap Page} (hs : s.stage = .idle) : rank input s ≤ 1 := by
  unfold rank; rw [hs]; (try dsimp only); split_ifs <;> omega

theorem rank_of_afterLevel {s : Snap Page} {e : ℤ} (hs : s.stage = afterLevel input e) :
    rank input s ≤ 2 * (maxLevel input - e).toNat + 1 := by
  unfold afterLevel at hs
  split_ifs at hs with h
  · unfold rank; rw [hs]; (try simp only); omega
  · have := rank_idle_le (input := input) hs; omega

theorem measure_initial_lt : measure input (initialSnap input) < fuel input := by
  have h1 := List.countP_le_length (p := fun ρ => decide (ρ.arrival ∈ arrivalTimes input))
    (l := input.requests)
  have h2 := arrivalTimes_length_le (input := input)
  have h3 : rank input (initialSnap input) ≤ 1 := rank_idle_le rfl
  simp only [measure, initialSnap, fuel, List.length_nil, add_zero] at h3 ⊢
  have h : ((arrivalTimes input).length +
      input.requests.countP (fun ρ => decide (ρ.arrival ∈ arrivalTimes input))) *
      (2 * numLevels input + 4) ≤
      (4 * input.requests.length) * (2 * numLevels input + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (4 * input.requests.length + 1) * (2 * numLevels input + 4) =
      4 * input.requests.length * (2 * numLevels input + 4) + (2 * numLevels input + 4) := by ring
  exact lt_of_le_of_lt (add_le_add h h3) (by rw [h4]; omega)

/-! ### Preservation -/

section

variable (hv : input.Valid)
include hv

theorem levelLen_nonneg (x : Page → ℝ) (p : Page) (e : ℤ) : 0 ≤ levelLen input x p e := by
  unfold levelLen
  have hL := Instance.L_pos hv
  have hW := PagingWithDelay.PMD.levelWeight_pos e
  have : L * levelWeight e ≤ 2 * L * levelWeight e := by nlinarith
  have := min_le_min_right (serviceEnd input x p) this
  linarith

theorem deposit_nonneg {x : Page → ℝ} {p : Page} {budget : ℤ → ℝ} (hb : ∀ e, 0 ≤ budget e)
    (e : ℤ) : 0 ≤ deposit input x p budget e := by
  unfold deposit
  split_ifs
  · exact add_nonneg (hb e) (levelLen_nonneg hv x p e)
  · exact hb e

/-- A critical service is on a page with a pending request. -/
theorem Inv.exists_pending_of_triggerPage {s : Snap Page} (hs : Inv input s) {p : Page}
    (hp : triggerPage input s = some p) : ∃ ρ ∈ s.pending, ρ.page = p :=
  exists_pending_of_critical (triggerPage_spec hp) (hs.claims p) (hv.weight_pos p)

theorem Inv.step {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) :
    Inv input s' ∧ Started input s' ∧ measure input s' < measure input s := by
  have hK : 2 * (numLevels input) + 4 =
      2 * (maxLevel input - minLevel input).toNat + 6 := by
    have := PagingWithDelay.PMD.minLevel_le_maxLevel hv
    simp only [numLevels]; omega
  have hvb := hv
  cases m with
  | tick t =>
    obtain ⟨hst, hnone, -, hup, rfl⟩ := next_tick h
    obtain ⟨A, hA⟩ := hs.upc
    have hpw := hs.upcoming_pairwise
    rw [hup] at hpw
    have hnow : s.now ≤ t := hs.now_le_upcoming (by rw [hup]; simp)
    have hnd : t ∉ s.upcoming.tail := fun ht => lt_irrefl t (List.rel_of_pairwise_cons hpw ht)
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hkeep : ∀ ρ ∈ s.pending, ρ ∈ ((s.pending ++ input.requests.filter
        fun ρ => decide (ρ.arrival = t)).filter fun ρ => decide (s.x ρ.page ≠ δ)) := by
      intro ρ hρ
      simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
      have := hs.pend_delta ρ hρ
      rw [hbase] at this
      exact ⟨Or.inl hρ, ne_of_gt this⟩
    have hstart : Started input ({ s with
        now := t
        upcoming := s.upcoming.tail
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) } : Snap Page) := by
      intro a ha
      exact List.rel_of_pairwise_cons hpw ha
    refine ⟨⟨⟨A ++ [t], by rw [hA, hup]; simp⟩, Or.inr hstart, ?_, ?_, ?_, ?_, hs.budget,
      hs.claims, ?_⟩, hstart, ?_⟩
    · intro ρ hρ
      try dsimp only at hρ
      simp only [List.mem_filter, List.mem_append, decide_eq_true_eq] at hρ
      rcases hρ.1 with hold | hnew
      · obtain ⟨hreq, ha, hnu⟩ := hs.pend ρ hold
        refine ⟨hreq, ha.trans hnow, fun h' => hnu ?_⟩
        rw [hup]; exact List.mem_cons_of_mem _ h'
      · refine ⟨hnew.1, hnew.2.le, ?_⟩
        try dsimp only
        rw [hnew.2]; exact hnd
    · intro ρ hρ
      try dsimp only at hρ
      simp only [List.mem_filter, decide_eq_true_eq] at hρ
      show δ < baseOf s ρ.page
      rw [hbase]
      have := (hs.rest.1 ρ.page).1
      rw [hbase] at this
      exact lt_of_le_of_ne this (Ne.symm hρ.2)
    · exact hs.rest
    · intro e b hb; simp [hst] at hb
    · intro q hq
      obtain ⟨ρ, hρ, hρq⟩ := hs.claims_pos q hq
      exact ⟨ρ, hkeep ρ hρ, hρq⟩
    · have hr := rank_idle_le (input := input) hst
      have hr' := rank_idle_le (input := input) (s := { s with
        now := t
        upcoming := s.upcoming.tail
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) }) hst
      simp only [measure]
      have hc1 := countP_mem_cons input.requests hnd
      rw [← hup] at hc1
      have hl : s.upcoming.length = s.upcoming.tail.length + 1 := by
        rw [hup]; simp
      have hf := List.length_filter_le (fun ρ : Request Page => decide (s.x ρ.page ≠ δ))
        (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t))
      rw [List.length_append] at hf
      have key : s.upcoming.tail.length +
          ((s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
            fun ρ => decide (s.x ρ.page ≠ δ)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming.tail)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | advance t =>
    obtain ⟨hst, hnone, hadv, ht, rfl⟩ := next_advance h
    have hc := hs.continuous hv
    have hlt : s.now < t := ht ▸ now_lt_sInf_triggerTimes hc hadv.1 hnone
    have hpw := hs.upcoming_pairwise
    have hstart : Started input ({ s with now := t } : Snap Page) := by
      intro a ha
      cases hup : s.upcoming with
      | nil => rw [hup] at ha; simp at ha
      | cons a0 rest =>
        have h0 : t < a0 := by rw [ht]; exact hadv.2 a0 (by rw [hup]; simp)
        try dsimp only at ha
        rw [hup] at ha hpw
        rcases List.mem_cons.mp ha with h1 | h1
        · rw [h1]; exact h0
        · exact h0.trans (List.rel_of_pairwise_cons hpw h1)
    have hb : baseOf ({ s with now := t } : Snap Page) = baseOf s := baseOf_congr rfl rfl
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, ?_, hs.preempt, hs.budget, hs.claims,
      hs.claims_pos⟩, hstart, ?_⟩
    · intro ρ hρ
      obtain ⟨h1, h2, h3⟩ := hs.pend ρ hρ
      exact ⟨h1, h2.trans hlt.le, h3⟩
    · rw [hb]; exact hs.pend_delta
    · rw [hb]; exact hs.rest
    · obtain ⟨p, hp⟩ := triggerPage_advance hc hadv.1
      rw [← ht] at hp
      have h1 : rank input s = 1 := by unfold rank; rw [hst, hnone]; rfl
      have h2 : rank input ({ s with now := t } : Snap Page) = 0 := by
        unfold rank; (try dsimp only); rw [hp, hst]; rfl
      simp only [measure]
      omega
  | critical p =>
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨ρ, hρ, hρp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hstart := hs.initial_or (Or.inr (List.ne_nil_of_mem hρ))
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hρp ▸ hbase ▸ hs.pend_delta ρ hρ
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hstart, ?_⟩
    · intro π hπ
      simp only [List.mem_filter] at hπ
      exact hs.pend π hπ.1
    · intro π hπ
      simp only [List.mem_filter, decide_eq_true_eq] at hπ
      simp only [baseOf]
      exact (hbase ▸ hs.pend_delta π hπ.1).trans_le
        (PagingWithDelay.PMD.le_criticalState hvb hrest hr hπ.2)
    · simpa [baseOf] using PagingWithDelay.PMD.criticalState_isRest hvb hrest hr
    · intro e b hb; simp at hb
    · exact deposit_nonneg hv hs.budget
    · intro q
      by_cases hq : q = p
      · subst hq; simp
      · simp only [Function.update_of_ne hq]
        exact (hs.claims q).trans (le_claimUpdate hv _ _ _ _ _ _)
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; simp at hq
      · simp only [Function.update_of_ne hqp] at hq
        have hmem : ∀ π ∈ s.pending, π.page = q → π ∈ s.pending.filter
            fun π => decide (π.page ≠ p) := by
          intro π hπ hπq
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hπ, hπq ▸ hqp⟩
        rcases lt_or_ge 0 (s.claims q) with h0 | h0
        · obtain ⟨π, hπ, hπq⟩ := hs.claims_pos q h0
          exact ⟨π, hmem π hπ hπq, hπq⟩
        · have hc0 : s.claims q = 0 := le_antisymm h0 (hs.claims q)
          have h1 := claimUpdate_le (input := input) s.x s.pending s.claims s.now p q
          have hov : 0 < overshoot input s.pending s.claims q s.now := by linarith
          have hpd := overshoot_pos_iff.mp hov
          obtain ⟨π, hπ, hπq⟩ := exists_pending_of_pageDelay_ne (p := q) (t := s.now)
            (by linarith [hv.weight_pos q])
          exact ⟨π, hmem π hπ hπq, hπq⟩
    · have hr0 : rank input s ≤ 1 := rank_idle_le hst
      have hr1 : rank input ({ s with
          x := criticalState input s.x p
          budget := deposit input s.x p s.budget
          pending := s.pending.filter fun π => decide (π.page ≠ p)
          claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
          stage := .examine (minLevel input) } : Snap Page) =
          2 * (maxLevel input - minLevel input).toNat + 3 := rfl
      simp only [measure]
      rw [hr1]
      have hlt : (s.pending.filter fun π => decide (π.page ≠ p)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨ρ, hρ, by simp [hρp]⟩
      have key : s.upcoming.length + (s.pending.filter fun π => decide (π.page ≠ p)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | skip e =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hbase' : baseOf ({ s with stage := afterLevel input e } : Snap Page) = s.x :=
      baseOf_of_not_preempt (by simpa using afterLevel_ne_preempt (input := input) e)
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, hs.budget, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · rw [hbase', ← hbase]; exact hs.pend_delta
    · rw [hbase', ← hbase]; exact hs.rest
    · intro e' b hb; exact absurd hb (afterLevel_ne_preempt e e' b)
    · have := rank_of_afterLevel (input := input)
        (s := { s with stage := afterLevel input e }) rfl
      have h1 : rank input s = 2 * (maxLevel input - e).toNat + 3 := by
        unfold rank; rw [hst]
      simp only [measure]
      omega
  | openHole e =>
    obtain ⟨hst, hcond, rfl⟩ := next_openHole h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, ?_, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · have h1 := hs.pend_delta; rw [hbase] at h1; exact h1
    · have h1 := hs.rest; rw [hbase] at h1; exact h1
    · intro e' b hb
      simp only [Stage.preempt.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨rfl, hcond.2⟩
    · intro e'
      by_cases he : e' = e
      · subst he
        simp only [Function.update_self]
        have h1 : holePayment input e' = levelWeight e' * (1 - δ) := rfl
        have h2 := PagingWithDelay.PMD.levelWeight_pos e'
        have h3 := Instance.delta_pos hv
        have h4 := hcond.1
        nlinarith
      · simp [Function.update_of_ne he, hs.budget e']
    · have h1 : rank input s = 2 * (maxLevel input - e).toNat + 3 := by
        unfold rank; rw [hst]
      have h2 : rank input ({ s with
          x := hole input s.x e
          budget := Function.update s.budget e (s.budget e - holePayment input e)
          stage := .preempt e s.x } : Snap Page) = 2 * (maxLevel input - e).toNat + 2 := rfl
      simp only [measure]
      omega
  | trip e π =>
    obtain ⟨⟨b, hst⟩, hπ, hcost, rfl⟩ := next_trip h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hπmem : π ∈ s.pending := by
      have := List.argmin_mem hπ
      exact (List.mem_filter.mp this).1
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, hs.rest, hs.preempt, ?_, ?_, ?_⟩, hstart, ?_⟩
    · intro ρ hρ
      exact hs.pend ρ (List.mem_filter.mp hρ).1
    · intro ρ hρ
      exact hs.pend_delta ρ (List.mem_filter.mp hρ).1
    · -- the round trip costs `w_q (x_q - δ) ≤ w_q ≤ W ≤ B_W`
      have htrip : tripCost input s.x π.page ≤ levelWeight e := by
        have hlev : level input π.page ≤ e := by
          simpa using (List.mem_filter.mp (List.argmin_mem hπ)).2
        have hrest : IsRest input b := by
          have := hs.rest; simpa [baseOf, hst] using this
        have h1 := PagingWithDelay.PMD.hole_le_one hvb hrest.1 e π.page
        have hd := Instance.delta_pos hv
        have hw := hv.weight_pos π.page
        have hW := (PagingWithDelay.PMD.level_le_iff hvb π.page e).1 hlev
        unfold tripCost
        rw [(hs.preempt e b hst).1]
        nlinarith
      intro e'
      by_cases he : e' = e
      · subst he; simp; linarith
      · simp [Function.update_of_ne he, hs.budget e']
    · intro q
      by_cases hq : q = π.page
      · subst hq; simp
      · simp only [Function.update_of_ne hq]; exact hs.claims q
    · intro q hq
      by_cases hqp : q = π.page
      · subst hqp; simp at hq
      · simp only [Function.update_of_ne hqp] at hq
        obtain ⟨ρ, hρ, hρq⟩ := hs.claims_pos q hq
        refine ⟨ρ, ?_, hρq⟩
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hρ, hρq ▸ hqp⟩
    · have h1 : rank input s = 2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; rw [hst]
      have h2 : rank input ({ s with
          budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
          pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
          claims := Function.update s.claims π.page 0 } : Snap Page) =
          2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; (try simp only); rw [hst]
      simp only [measure]
      rw [h1, h2]
      have hlt : (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨π, hπmem, by simp⟩
      have key : s.upcoming.length + (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | closeHole e stop =>
    obtain ⟨b, hst, -, rfl⟩ := next_closeHole h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = b := by simp [baseOf, hst]
    have hbase' : baseOf ({ s with x := b, stage := afterLevel input e } : Snap Page) = b :=
      baseOf_of_not_preempt (by simpa using afterLevel_ne_preempt (input := input) e)
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, hs.budget, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · rw [hbase', ← hbase]; exact hs.pend_delta
    · rw [hbase', ← hbase]; exact hs.rest
    · intro e' b' hb; exact absurd hb (afterLevel_ne_preempt e e' b')
    · have := rank_of_afterLevel (input := input)
        (s := { s with x := b, stage := afterLevel input e }) rfl
      have h1 : rank input s = 2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; rw [hst]
      simp only [measure]
      omega

end

/-! ### Consequences of one move -/

theorem Inv.next_now (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) :
    s.now ≤ s'.now ∧
      ((∀ t, m ≠ .tick t) → (∀ t, m ≠ .advance t) →
        s'.now = s.now ∧ s'.upcoming = s.upcoming) ∧
      (∀ t, m = .tick t → s'.now = t ∧ s.upcoming = t :: s'.upcoming ∧
        (Started input s → s.now < t)) ∧
      (∀ t, m = .advance t → s'.now = t ∧ s'.upcoming = s.upcoming ∧ s.now < t) := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, hup, rfl⟩ := next_tick h
    have hnow : s.now ≤ t := hs.now_le_upcoming (by rw [hup]; simp)
    refine ⟨hnow, fun ht' => absurd rfl (ht' t), ?_, fun _ h => by cases h⟩
    rintro t' ⟨⟩
    exact ⟨rfl, hup, fun hst => hst t (by rw [hup]; simp)⟩
  | advance t =>
    obtain ⟨-, hnone, hadv, ht, rfl⟩ := next_advance h
    have hlt : s.now < t := ht ▸ now_lt_sInf_triggerTimes (hs.continuous hv) hadv.1 hnone
    refine ⟨hlt.le, fun _ ha => absurd rfl (ha t), fun _ h => (by cases h), ?_⟩
    rintro t' ⟨⟩
    exact ⟨rfl, rfl, hlt⟩
  | critical ρ =>
    obtain ⟨-, -, rfl⟩ := next_critical h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩

/-- A request enters the pending list only at the tick at its arrival time. -/
theorem next_pending_new {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) {ρ : Request Page}
    (h' : ρ ∈ s'.pending) (hnot : ρ ∉ s.pending) :
    m = .tick ρ.arrival ∧ ρ ∈ input.requests := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_tick h
    simp only [List.mem_filter, List.mem_append, decide_eq_true_eq] at h'
    rcases h'.1 with h1 | h1
    · exact absurd h1 hnot
    · exact ⟨by rw [h1.2], h1.1⟩
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    exact absurd h' hnot
  | critical ρ' =>
    obtain ⟨-, -, rfl⟩ := next_critical h
    exact absurd (List.mem_filter.mp h').1 hnot
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact absurd h' hnot
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact absurd h' hnot
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    exact absurd (List.mem_filter.mp h').1 hnot
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact absurd h' hnot

theorem next_baseOf_of_not_critical {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) (hm : ∀ p, m ≠ .critical p) :
    baseOf s' = baseOf s := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_tick h
    rfl
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    rfl
  | critical p => exact absurd rfl (hm p)
  | skip e =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    rw [baseOf_of_not_preempt (s := s) (by simp [hst])]
    apply baseOf_of_not_preempt
    intro e' b; exact afterLevel_ne_preempt e e' b
  | openHole e =>
    obtain ⟨hst, -, rfl⟩ := next_openHole h
    rw [baseOf_of_not_preempt (s := s) (by simp [hst])]
    rfl
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    rfl
  | closeHole e stop =>
    obtain ⟨b, hst, -, rfl⟩ := next_closeHole h
    have : baseOf s = b := by simp [baseOf, hst]
    rw [this]
    apply baseOf_of_not_preempt
    intro e' b'; exact afterLevel_ne_preempt e e' b'

/-- `obs:monotone`, one move: the base state of a page `q` does not decrease unless the move is a critical service on `q`. -/
theorem Inv.baseOf_le_next (hv : input.Valid) {s s' : Snap Page} {m : Move Page}
    (hs : Inv input s) (h : next input s = some (m, s')) {q : Page} (hm : m ≠ .critical q) :
    baseOf s q ≤ baseOf s' q := by
  by_cases hc : ∃ p, m = .critical p
  · obtain ⟨p, rfl⟩ := hc
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨ρ, hρ, hρp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hρp ▸ hbase ▸ hs.pend_delta ρ hρ
    have hqp : q ≠ p := fun h => hm (h ▸ rfl)
    rw [hbase]
    simp only [baseOf]
    exact PagingWithDelay.PMD.le_criticalState hv hrest hr hqp
  · push_neg at hc
    rw [next_baseOf_of_not_critical h hc]

theorem next_of_preempt {s s' : Snap Page} {m : Move Page} {e : ℤ} {b : Page → ℝ}
    (hs : s.stage = .preempt e b) (h : next input s = some (m, s')) :
    (∃ π, m = .trip e π ∧ s'.stage = .preempt e b) ∨
      (∃ stop, m = .closeHole e stop ∧ s'.stage = afterLevel input e) := by
  cases m with
  | tick t => obtain ⟨hst, -⟩ := next_tick h; simp [hst] at hs
  | advance t => obtain ⟨hst, -⟩ := next_advance h; simp [hst] at hs
  | critical ρ => obtain ⟨hst, -⟩ := next_critical h; simp [hst] at hs
  | skip e => obtain ⟨hst, -⟩ := next_skip h; simp [hst] at hs
  | openHole e => obtain ⟨hst, -⟩ := next_openHole h; simp [hst] at hs
  | trip e' π =>
    obtain ⟨⟨b', hst⟩, -, -, rfl⟩ := next_trip h
    rw [hst] at hs
    simp only [Stage.preempt.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inl ⟨π, rfl, hst⟩
  | closeHole e' stop =>
    obtain ⟨b', hst, -, rfl⟩ := next_closeHole h
    rw [hst] at hs
    simp only [Stage.preempt.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inr ⟨stop, rfl, rfl⟩

theorem next_of_examine {s s' : Snap Page} {m : Move Page} {e : ℤ}
    (hs : s.stage = .examine e) (h : next input s = some (m, s')) :
    (m = .skip e ∧ s'.stage = afterLevel input e) ∨
      (m = .openHole e ∧ s'.stage = .preempt e s.x) := by
  cases m with
  | tick t => obtain ⟨hst, -⟩ := next_tick h; simp [hst] at hs
  | advance t => obtain ⟨hst, -⟩ := next_advance h; simp [hst] at hs
  | critical ρ => obtain ⟨hst, -⟩ := next_critical h; simp [hst] at hs
  | skip e' =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    rw [hst] at hs; simp only [Stage.examine.injEq] at hs; subst hs
    exact Or.inl ⟨rfl, rfl⟩
  | openHole e' =>
    obtain ⟨hst, -, rfl⟩ := next_openHole h
    rw [hst] at hs; simp only [Stage.examine.injEq] at hs; subst hs
    exact Or.inr ⟨rfl, rfl⟩
  | trip e' π => obtain ⟨⟨b', hst⟩, -⟩ := next_trip h; simp [hst] at hs
  | closeHole e' stop => obtain ⟨b', hst, -⟩ := next_closeHole h; simp [hst] at hs

theorem next_to_preempt {s s' : Snap Page} {m : Move Page} {e : ℤ} {b : Page → ℝ}
    (h : next input s = some (m, s')) (hs' : s'.stage = .preempt e b) :
    m = .openHole e ∨ (∃ π, m = .trip e π ∧ s.stage = .preempt e b) := by
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_tick h
    (try simp only at hs'); rw [hst] at hs'; simp at hs'
  | advance t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_advance h
    (try simp only at hs'); rw [hst] at hs'; simp at hs'
  | critical ρ => obtain ⟨-, -, rfl⟩ := next_critical h; simp at hs'
  | skip e' => obtain ⟨-, -, rfl⟩ := next_skip h; exact absurd hs' (afterLevel_ne_preempt e' e b)
  | openHole e' =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    simp only [Stage.preempt.injEq] at hs'
    rw [hs'.1]; exact Or.inl rfl
  | trip e' π =>
    obtain ⟨⟨b', hst⟩, -, -, rfl⟩ := next_trip h
    try simp only at hs'
    rw [hst] at hs' ⊢
    simp only [Stage.preempt.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    exact Or.inr ⟨π, rfl, rfl⟩
  | closeHole e' stop =>
    obtain ⟨b', -, -, rfl⟩ := next_closeHole h
    exact absurd hs' (afterLevel_ne_preempt e' e b)

/-- A request leaves the pending list only by a visit of its page (a critical service on it or a round trip to it), which records a waypoint at the current time with `x_p = δ`. -/
theorem Inv.removed (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) {ρ : Request Page} (hρ : ρ ∈ s.pending)
    (hρ' : ρ ∉ s'.pending) :
    (m = .critical ρ.page ∨ ∃ e π, m = .trip e π ∧ π.page = ρ.page) ∧
      ∃ v ∈ waypoints input s m, v.time = s.now ∧ v.state ρ.page = δ := by
  have hvb := hv
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_tick h
    exfalso; apply hρ'
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have := hs.pend_delta ρ hρ
    rw [hbase] at this
    simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
    exact ⟨Or.inl hρ, ne_of_gt this⟩
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    exact absurd hρ hρ'
  | critical p =>
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨π, hπ, hπp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hπp ▸ hbase ▸ hs.pend_delta π hπ
    simp only [List.mem_filter, decide_eq_true_eq, not_and, not_not] at hρ'
    have hpage := hρ' hρ
    refine ⟨Or.inl (by rw [hpage]), ⟨s.now, criticalState input s.x p⟩,
      by simp [waypoints], rfl, ?_⟩
    try simp only
    rw [hpage]
    exact PagingWithDelay.PMD.criticalState_self hvb hrest hr
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact absurd hρ hρ'
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact absurd hρ hρ'
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    simp only [List.mem_filter, decide_eq_true_eq, not_and, not_not] at hρ'
    have hpage := hρ' hρ
    refine ⟨Or.inr ⟨e, π, rfl, hpage.symm⟩, ⟨s.now, Function.update s.x π.page δ⟩,
      by simp [waypoints], rfl, ?_⟩
    try simp only
    rw [hpage]
    simp
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact absurd hρ hρ'

/-- A request arriving at a tick that does not become pending is served on arrival: `x_p = δ` in the tick's waypoint. -/
theorem next_tick_served {s s' : Snap Page} {t : ℝ} (h : next input s = some (.tick t, s'))
    {ρ : Request Page} (hρ : ρ ∈ input.requests) (ha : ρ.arrival = t) (hρ' : ρ ∉ s'.pending) :
    s.x ρ.page = δ ∧ (⟨t, s.x⟩ : Waypoint Page) ∈
      waypoints input s (.tick t) := by
  obtain ⟨-, -, -, -, rfl⟩ := next_tick h
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq, not_and, not_not] at hρ'
  exact ⟨hρ' (Or.inr ⟨hρ, ha⟩), by simp [waypoints]⟩

section

variable (hv : input.Valid)
include hv

/-- The run from the initial state ends within `fuel` moves. -/
theorem next_run_initial :
    next input (run input (fuel input) (initialSnap input)).2 = none :=
  next_run_final (measure input) (Inv input)
    (fun _ _ _ hs h => ⟨(hs.step hv h).1, (hs.step hv h).2.2⟩)
    (fuel input) (initialSnap input) (inv_initial hv) measure_initial_lt

end

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Basic` -/
section

/-!
# The run of `PMD`: log, snapshots, and their invariants

`snapAt i` is the loop state before log entry `i` (after entry `i - 1`); `snapAt (log.length)` is the final state. This file collects what the analysis uses about the run: the chain of moves, the semantics of each move, the order of times, the invariants (`lem:inv`), pending-list and claims facts, `obs:monotone`, and the structure of preemptive services and level loops.
-/

namespace PagingWithDelay

namespace PMD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage IsRest IsFrac
  restMass)

noncomputable section

variable (input : Instance Page)

/-- The final loop state. -/
def finalSnap : Snap Page := (run input (fuel input) (initialSnap input)).2

/-- The loop state before entry `i` of the log (the final state for `i ≥ log.length`). -/
def snapAt (i : ℕ) : Snap Page :=
  if h : i < (log input).length then ((log input)[i]).1 else finalSnap input

/-- The move of entry `i`. -/
def moveAt {input : Instance Page} (i : ℕ) (h : i < (log input).length) : Move Page :=
  ((log input)[i]).2

/-- The time of entry `i`: the time after its move. -/
def entryTime (i : ℕ) : ℝ := (snapAt input (i + 1)).now

/-- The state outside the current preemptive service: the state the hole was opened from, or the current state. -/
def baseState (s : Snap Page) : Page → ℝ :=
  match s.stage with
  | .preempt _ base => base
  | _ => s.x

variable {input}

theorem snapAt_eq_runSnap (i : ℕ) :
    snapAt input i = runSnap input (fuel input) (initialSnap input) i := rfl

theorem snapAt_of_ge {i : ℕ} (hi : (log input).length ≤ i) :
    snapAt input i = finalSnap input := by
  unfold snapAt; rw [dif_neg (by omega)]

theorem baseState_eq_baseOf (s : Snap Page) : baseState s = baseOf s := rfl

theorem baseState_of_preempt' {s : Snap Page} {e : ℤ} {b : Page → ℝ}
    (hs : s.stage = .preempt e b) : baseState s = b := by
  simp [baseState, hs]

theorem baseState_of_not_preempt {s : Snap Page} (hs : ∀ e b, s.stage ≠ .preempt e b) :
    baseState s = s.x :=
  baseOf_of_not_preempt hs

section

variable (hv : input.Valid)
include hv

/-! ### The chain of moves -/

theorem snapAt_zero : snapAt input 0 = initialSnap input := by
  rw [snapAt_eq_runSnap]; exact runSnap_zero _ _

theorem next_snapAt (i : ℕ) (h : i < (log input).length) :
    next input (snapAt input i) = some (moveAt i h, snapAt input (i + 1)) := by
  rw [snapAt_eq_runSnap, snapAt_eq_runSnap]
  exact next_runSnap _ _ i h

theorem next_final : next input (snapAt input (log input).length) = none := by
  rw [snapAt_of_ge le_rfl]; exact next_run_initial hv

theorem inv_snapAt (i : ℕ) : Inv input (snapAt input i) := by
  induction i with
  | zero => rw [snapAt_zero hv]; exact inv_initial hv
  | succ i ih =>
    by_cases hi : i < (log input).length
    · exact (ih.step hv (next_snapAt hv i hi)).1
    · rw [snapAt_of_ge (by omega)]; rw [snapAt_of_ge (by omega)] at ih; exact ih

theorem started_succ {i : ℕ} (hi : i < (log input).length) :
    Started input (snapAt input (i + 1)) :=
  ((inv_snapAt hv i).step hv (next_snapAt hv i hi)).2.1

theorem started_of_pos {i : ℕ} (hi : i ≤ (log input).length) (h0 : 0 < i) :
    Started input (snapAt input i) := by
  have := started_succ hv (i := i - 1) (by omega)
  rwa [show i - 1 + 1 = i by omega] at this

theorem now_succ (i : ℕ) : (snapAt input i).now ≤ (snapAt input (i + 1)).now := by
  by_cases hi : i < (log input).length
  · exact ((inv_snapAt hv i).next_now hv (next_snapAt hv i hi)).1
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

/-- At the end, all arrival times are processed, nothing is pending, the loop is idle, and `eq:trigger` holds for no page from now on. -/
theorem final_spec :
    (snapAt input (log input).length).upcoming = [] ∧
      (snapAt input (log input).length).pending = [] ∧
      (snapAt input (log input).length).stage = .idle ∧
      triggerTimes input (snapAt input (log input).length) = ∅ := by
  have hn := next_eq_none (next_final hv)
  have hinv := inv_snapAt hv (log input).length
  refine ⟨hn.2.2.2, ?_, hn.1, Set.not_nonempty_iff_eq_empty.mp hn.2.2.1⟩
  rw [List.eq_nil_iff_forall_not_mem]
  intro ρ hρ
  exact hn.2.2.1 (triggerTimes_nonempty_of_valid hv (fun π hπ => (hinv.pend π hπ).1)
    (fun π hπ => (hinv.pend π hπ).2.1) hρ)

/-! ### Times -/

theorem now_mono {i j : ℕ} (hij : i ≤ j) : (snapAt input i).now ≤ (snapAt input j).now := by
  exact monotone_nat_of_le_succ (f := fun i => (snapAt input i).now) (now_succ hv) hij

theorem entryTime_mono {i j : ℕ} (hij : i ≤ j) : entryTime input i ≤ entryTime input j :=
  now_mono hv (by omega)

theorem now_le_entryTime (i : ℕ) : (snapAt input i).now ≤ entryTime input i :=
  now_succ hv i

theorem upcoming_pairwise (i : ℕ) : (snapAt input i).upcoming.Pairwise (· < ·) :=
  (inv_snapAt hv i).upcoming_pairwise

theorem now_le_upcoming (i : ℕ) {a : ℝ} (ha : a ∈ (snapAt input i).upcoming) :
    (snapAt input i).now ≤ a :=
  (inv_snapAt hv i).now_le_upcoming ha

/-- After the first move, all upcoming arrival times are strictly later than now. -/
theorem now_lt_upcoming {i : ℕ} (hi : i ≤ (log input).length) (h0 : 0 < i) {a : ℝ}
    (ha : a ∈ (snapAt input i).upcoming) : (snapAt input i).now < a :=
  started_of_pos hv hi h0 a ha

/-- A tick at `t` precedes all entries at time `t`: every entry before it has time `< t`. -/
theorem entryTime_lt_of_tick {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) {j : ℕ} (hj : j < i) : entryTime input j < t := by
  have hst := started_of_pos hv h.le (by omega)
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  have hn := ((inv_snapAt hv i).next_now hv hnext).2.2.1 t rfl
  have h1 := hn.2.2 hst
  have h2 := now_mono hv (i := j + 1) (j := i) (by omega)
  unfold entryTime
  linarith

theorem entryTime_tick {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) : entryTime input i = t := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact (((inv_snapAt hv i).next_now hv hnext).2.2.1 t rfl).1

theorem entryTime_advance {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .advance t) : entryTime input i = t ∧ (snapAt input i).now < t := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  have := ((inv_snapAt hv i).next_now hv hnext).2.2.2 t rfl
  exact ⟨this.1, this.2.2⟩

/-- Moves other than ticks and advances happen at the current time. -/
theorem entryTime_of_not_tick {i : ℕ} (h : i < (log input).length)
    (hm : ∀ t, moveAt i h ≠ .tick t) (ha : ∀ t, moveAt i h ≠ .advance t) :
    entryTime input i = (snapAt input i).now := by
  exact (((inv_snapAt hv i).next_now hv (next_snapAt hv i h)).2.1 hm ha).1

theorem upcoming_succ_of_not_tick {i : ℕ} (h : i < (log input).length)
    (hm : ∀ t, moveAt i h ≠ .tick t) :
    (snapAt input (i + 1)).upcoming = (snapAt input i).upcoming := by
  by_cases ha : ∃ t, moveAt i h = .advance t
  · obtain ⟨t, ht⟩ := ha
    have hnext := next_snapAt hv i h
    rw [ht] at hnext
    exact (((inv_snapAt hv i).next_now hv hnext).2.2.2 t rfl).2.1
  · push_neg at ha
    exact (((inv_snapAt hv i).next_now hv (next_snapAt hv i h)).2.1 hm ha).2

/-- Every arrival time is ticked. -/
theorem exists_tick_arrival {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ i, ∃ h : i < (log input).length, moveAt i h = .tick ρ.arrival := by
  have key : ∀ n, ρ.arrival ∉ (snapAt input n).upcoming →
      ∃ i, ∃ h : i < (log input).length, moveAt i h = .tick ρ.arrival := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [snapAt_zero hv] at hn
      exact absurd (arrival_mem_arrivalTimes hρ) hn
    | succ n ih =>
      intro hn
      by_cases hmem : ρ.arrival ∈ (snapAt input n).upcoming
      · by_cases hlt : n < (log input).length
        · by_cases htick : ∃ t, moveAt n hlt = .tick t
          · obtain ⟨t, ht⟩ := htick
            have hnext := next_snapAt hv n hlt
            rw [ht] at hnext
            have hup := (((inv_snapAt hv n).next_now hv hnext).2.2.1 t rfl).2.1
            rw [hup] at hmem
            rcases List.mem_cons.mp hmem with h1 | h1
            · exact ⟨n, hlt, by rw [ht, h1]⟩
            · exact absurd h1 hn
          · push_neg at htick
            rw [upcoming_succ_of_not_tick hv hlt htick] at hn
            exact absurd hmem hn
        · rw [snapAt_of_ge (by omega)] at hn hmem
          exact absurd hmem hn
      · exact ih hmem
  apply key (log input).length
  rw [(final_spec hv).1]
  simp

/-- Between two moves, `eq:trigger` holds for no page: at a tick or an advance at entry `i`, it holds for no page (w.r.t. `snapAt i`) at any time in `[now, entryTime i)`. -/
theorem not_triggered_before {i : ℕ} (h : i < (log input).length)
    (hm : (∃ t, moveAt i h = .tick t) ∨ (∃ t, moveAt i h = .advance t)) {τ : ℝ}
    (hτ1 : (snapAt input i).now ≤ τ) (hτ2 : τ < entryTime input i) (p : Page) :
    ¬ TriggerCond input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims τ p := by
  intro hp
  have hmem : τ ∈ triggerTimes input (snapAt input i) := ⟨hτ1, p, hp⟩
  have hle := sInf_triggerTimes_le hmem
  have hnext := next_snapAt hv i h
  rcases hm with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at hnext
    obtain ⟨-, -, hnadv, hup, -⟩ := next_tick hnext
    rw [entryTime_tick hv h ht] at hτ2
    apply hnadv
    refine ⟨⟨τ, hmem⟩, ?_⟩
    rw [hup]
    intro a ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha
    by_contra hc
    push_neg at hc
    linarith
  · rw [ht] at hnext
    obtain ⟨-, -, -, ht', -⟩ := next_advance hnext
    rw [(entryTime_advance hv h ht).1, ht'] at hτ2
    linarith

/-! ### Pending requests -/

/-- Pending requests are requests of the input that have arrived (their arrival time has been ticked). -/
theorem pending_spec {i : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input i).pending) :
    ρ ∈ input.requests ∧ ρ.arrival ≤ (snapAt input i).now ∧
      ρ.arrival ∉ (snapAt input i).upcoming :=
  (inv_snapAt hv i).pend ρ hρ

/-- The key monotonicity: a request pending before entry `j` that had arrived by the time of an earlier entry `i` was already pending after entry `i`. -/
theorem pending_of_later {i j : ℕ} (hij : i < j) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input j).pending) (ha : ρ.arrival ≤ entryTime input i) :
    ρ ∈ (snapAt input (i + 1)).pending := by
  by_contra hnot
  have key : ∀ n, i + 1 ≤ n → ρ ∉ (snapAt input n).pending := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hnot
    | succ n hn ih =>
      intro hmem
      by_cases hlt : n < (log input).length
      · have hnext := next_snapAt hv n hlt
        obtain ⟨hm, -⟩ := next_pending_new hnext hmem ih
        rw [hm] at hnext
        have hN := ((inv_snapAt hv n).next_now hv hnext).2.2.1 _ rfl
        have hst := started_of_pos hv hlt.le (by omega)
        have h1 := hN.2.2 hst
        have h2 := now_mono hv (i := i + 1) (j := n) hn
        unfold entryTime at ha
        linarith
      · rw [snapAt_of_ge (by omega)] at hmem ih
        exact ih hmem
  exact key j (by omega) hρ

/-- A request enters the pending list only at the tick at its arrival time. -/
theorem pending_new {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (h1 : ρ ∈ (snapAt input (i + 1)).pending) (h0 : ρ ∉ (snapAt input i).pending) :
    moveAt i h = .tick ρ.arrival ∧ ρ ∈ input.requests :=
  next_pending_new (next_snapAt hv i h) h1 h0

open scoped InstanceNotation in
/-- Part of `lem:inv`: every pending request is on a page with base missing mass `> δ`. -/
theorem delta_lt_baseState_of_pending {i : ℕ} {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) : δ < baseState (snapAt input i) ρ.page :=
  (inv_snapAt hv i).pend_delta ρ hρ

/-! ### States and budgets (`lem:inv`(a)) -/

theorem baseState_isRest (i : ℕ) : IsRest input (baseState (snapAt input i)) := by
  rw [baseState_eq_baseOf]; exact (inv_snapAt hv i).rest

theorem x_eq_baseState {i : ℕ} (hs : ∀ e b, (snapAt input i).stage ≠ .preempt e b) :
    (snapAt input i).x = baseState (snapAt input i) := by
  rw [baseState_eq_baseOf, baseOf_of_not_preempt hs]

open scoped InstanceNotation in
theorem x_eq_hole {i : ℕ} {e : ℤ} {b : Page → ℝ} (hs : (snapAt input i).stage = .preempt e b) :
    (snapAt input i).x = hole input b e ∧
      1 - δ ≤
        ∑ j ∈ Finset.univ.filter (fun j => level input j ≤ e), (1 - b j) := by
  exact (inv_snapAt hv i).preempt e b hs

/-- The current state is at least the base state (`obs:monotone`: opening a hole only increases missing masses). -/
theorem baseState_le_x (i : ℕ) (q : Page) :
    baseState (snapAt input i) q ≤ (snapAt input i).x q := by
  by_cases hs : ∃ e b, (snapAt input i).stage = .preempt e b
  · obtain ⟨e, b, hs⟩ := hs
    have hb := baseState_isRest hv i
    rw [baseState_of_preempt' hs] at hb ⊢
    rw [(x_eq_hole hv hs).1]
    exact PagingWithDelay.PMD.le_hole hv hb.1 e q
  · push_neg at hs
    rw [x_eq_baseState hv hs]

open scoped InstanceNotation in
/-- Part of `lem:inv`: every pending request is on a page with missing mass `> δ`. -/
theorem delta_lt_of_pending {i : ℕ} {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) : δ < (snapAt input i).x ρ.page :=
  (delta_lt_baseState_of_pending hv hρ).trans_le (baseState_le_x hv i ρ.page)

theorem baseState_succ_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) :
    baseState (snapAt input (i + 1)) = baseState (snapAt input i) := by
  rw [baseState_eq_baseOf, baseState_eq_baseOf]
  exact next_baseOf_of_not_critical (next_snapAt hv i h) hm

/-- `obs:monotone`, one move: the base missing mass of `q` does not decrease, unless the move is a critical service on `q`. -/
theorem baseState_le_succ {i : ℕ} (h : i < (log input).length) {q : Page}
    (hm : moveAt i h ≠ .critical q) :
    baseState (snapAt input i) q ≤ baseState (snapAt input (i + 1)) q :=
  (inv_snapAt hv i).baseOf_le_next hv (next_snapAt hv i h) hm

/-- `obs:monotone`: between two log indices with no critical service on `q` in between, the base missing mass of `q` does not decrease (round trips do not change the base state). -/
theorem baseState_mono {i j : ℕ} (hij : i ≤ j) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), i ≤ l → l < j → moveAt l hl ≠ .critical q) :
    baseState (snapAt input i) q ≤ baseState (snapAt input j) q := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    refine (ih fun l hl h1 h2 => hno l hl h1 (by omega)).trans ?_
    by_cases hlt : j < (log input).length
    · exact baseState_le_succ hv hlt (hno j hlt hj (by omega))
    · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

/-- `obs:monotone` for the current state: between `i` and `j` without a critical service on `q`, the missing mass of `q` at `j` is at least its base missing mass at `i`. -/
theorem baseState_le_x_of_mono {i j : ℕ} (hij : i ≤ j) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), i ≤ l → l < j → moveAt l hl ≠ .critical q) :
    baseState (snapAt input i) q ≤ (snapAt input j).x q :=
  (baseState_mono hv hij hno).trans (baseState_le_x hv j q)

theorem budget_nonneg (i : ℕ) (e : ℤ) : 0 ≤ (snapAt input i).budget e := by
  exact (inv_snapAt hv i).budget e

theorem claims_nonneg (i : ℕ) (q : Page) : 0 ≤ (snapAt input i).claims q :=
  (inv_snapAt hv i).claims q

/-! ### Semantics of the moves -/

open scoped InstanceNotation in
theorem tick_spec {i : ℕ} (h : i < (log input).length) {t : ℝ} (hm : moveAt i h = .tick t) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = none ∧
    ¬ AdvanceCond input (snapAt input i) ∧
    (snapAt input i).upcoming = t :: (snapAt input (i + 1)).upcoming ∧
    (snapAt input (i + 1)) = { snapAt input i with
      now := t
      upcoming := (snapAt input i).upcoming.tail
      pending := ((snapAt input i).pending ++
          input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
        fun ρ => decide ((snapAt input i).x ρ.page ≠ δ) } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨hst, hn, ha, hup, heq⟩ := next_tick hnext
  refine ⟨hst, hn, ha, ?_, heq⟩
  rw [heq]; exact hup

theorem advance_spec {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .advance t) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = none ∧
    AdvanceCond input (snapAt input i) ∧ t = sInf (triggerTimes input (snapAt input i)) ∧
    (∃ p, Critical input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims
      t p) ∧ (snapAt input i).now < t ∧
    (snapAt input (i + 1)) = { snapAt input i with now := t } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨hst, hn, ha, ht, heq⟩ := next_advance hnext
  have hc := (inv_snapAt hv i).continuous hv
  refine ⟨hst, hn, ha, ht, ht ▸ exists_critical_sInf ha.1,
    ht ▸ now_lt_sInf_triggerTimes hc ha.1 hn, heq⟩

theorem critical_spec {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = some p ∧
    (snapAt input (i + 1)) = { snapAt input i with
      x := criticalState input (snapAt input i).x p
      budget := deposit input (snapAt input i).x p (snapAt input i).budget
      pending := (snapAt input i).pending.filter fun π => decide (π.page ≠ p)
      claims := Function.update (claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p) p 0
      stage := .examine (minLevel input) } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_critical hnext

open scoped InstanceNotation in
/-- The facts behind a critical service on `p`: `p` is critical now (closed form of the trigger), has a pending request, and the state is a rest state with `x_p > δ`. -/
theorem critical_facts {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    Triggered input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims
        (snapAt input i).now p ∧
      (∃ ρ ∈ (snapAt input i).pending, ρ.page = p) ∧
      IsRest input (snapAt input i).x ∧ δ < (snapAt input i).x p ∧
      entryTime input i = (snapAt input i).now := by
  obtain ⟨hst, htp, -⟩ := critical_spec hv h hm
  obtain ⟨ρ, hρ, hρp⟩ := (inv_snapAt hv i).exists_pending_of_triggerPage hv htp
  have hx : (snapAt input i).x = baseState (snapAt input i) :=
    x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb)
  refine ⟨triggerPage_triggered ((inv_snapAt hv i).continuous hv) htp, ⟨ρ, hρ, hρp⟩, ?_, hρp ▸ delta_lt_of_pending hv hρ, ?_⟩
  · rw [hx]; exact baseState_isRest hv i
  · exact entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)

theorem skip_spec {i : ℕ} (h : i < (log input).length) {e : ℤ} (hm : moveAt i h = .skip e) :
    (snapAt input i).stage = .examine e ∧
    ¬ preemptCondition input (snapAt input i).x (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with stage := afterLevel input e } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_skip hnext

theorem openHole_spec {i : ℕ} (h : i < (log input).length) {e : ℤ}
    (hm : moveAt i h = .openHole e) :
    (snapAt input i).stage = .examine e ∧
    preemptCondition input (snapAt input i).x (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with
      x := hole input (snapAt input i).x e
      budget := Function.update (snapAt input i).budget e
        ((snapAt input i).budget e - holePayment input e)
      stage := .preempt e (snapAt input i).x } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_openHole hnext

theorem trip_spec {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) :
    (∃ b, (snapAt input i).stage = .preempt e b) ∧
    tripCandidate input (snapAt input i).pending (snapAt input i).now e = some π ∧
    levelWeight e ≤ (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with
      budget := Function.update (snapAt input i).budget e
        ((snapAt input i).budget e - tripCost input (snapAt input i).x π.page)
      pending := (snapAt input i).pending.filter fun ρ => decide (ρ.page ≠ π.page)
      claims := Function.update (snapAt input i).claims π.page 0 } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_trip hnext

theorem closeHole_spec {i : ℕ} (h : i < (log input).length) {e : ℤ}
    {stop : Option (Request Page)} (hm : moveAt i h = .closeHole e stop) :
    ∃ b, (snapAt input i).stage = .preempt e b ∧
    (match stop with
      | none => tripCandidate input (snapAt input i).pending (snapAt input i).now e = none
      | some π => tripCandidate input (snapAt input i).pending (snapAt input i).now e = some π ∧
          (snapAt input i).budget e < levelWeight e) ∧
    (snapAt input (i + 1)) = { snapAt input i with x := b, stage := afterLevel input e } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨b, h1, h2, h3⟩ := next_closeHole hnext
  refine ⟨b, h1, ?_, h3⟩
  cases stop with
  | none => exact h2
  | some π => exact h2

/-- Only visits (critical services and round trips) change the claims. -/
theorem claims_succ_of_not_visit {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π) :
    (snapAt input (i + 1)).claims = (snapAt input i).claims := by
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · rw [(tick_spec hv h hm).2.2.2.2]
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]
  · exact absurd hm (hc p)
  · rw [(skip_spec hv h hm).2.2]
  · rw [(openHole_spec hv h hm).2.2]
  · exact absurd hm (ht e π)
  · obtain ⟨b, -, -, he⟩ := closeHole_spec hv h hm
    rw [he]

/-- Only critical services, round trips and ticks change the pending list (ticks only add requests). -/
theorem pending_succ_of_not_visit {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π)
    (htk : ∀ t, moveAt i h ≠ .tick t) :
    (snapAt input (i + 1)).pending = (snapAt input i).pending := by
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · exact absurd hm (htk t)
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]
  · exact absurd hm (hc p)
  · rw [(skip_spec hv h hm).2.2]
  · rw [(openHole_spec hv h hm).2.2]
  · exact absurd hm (ht e π)
  · obtain ⟨b, -, -, he⟩ := closeHole_spec hv h hm
    rw [he]

/-! ### Serving requests -/

/-- A request leaves the pending list only by a visit of its page (a critical service on it or a round trip to it); the visit records a waypoint at the current time with `x_p = δ`. -/
theorem pending_removed {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    (moveAt i h = .critical ρ.page ∨ ∃ e π, moveAt i h = .trip e π ∧ π.page = ρ.page) ∧
      ∃ w ∈ waypoints input (snapAt input i) (moveAt i h),
        w.time = (snapAt input i).now ∧ w.state ρ.page = input.delta :=
  (inv_snapAt hv i).removed hv (next_snapAt hv i h) hρ hρ'

/-- A visit serves all pending requests on its page. -/
theorem pending_succ_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) {ρ : Request Page} :
    ρ ∈ (snapAt input (i + 1)).pending ↔ ρ ∈ (snapAt input i).pending ∧ ρ.page ≠ p := by
  rw [(critical_spec hv h hm).2.2]
  simp

theorem pending_succ_of_trip {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) {ρ : Request Page} :
    ρ ∈ (snapAt input (i + 1)).pending ↔ ρ ∈ (snapAt input i).pending ∧ ρ.page ≠ π.page := by
  rw [(trip_spec hv h hm).2.2.2]
  simp

open scoped InstanceNotation in
/-- A request ticked at entry `i` that does not become pending is served on arrival: its page has `x_p = δ` at the tick's waypoint `(t, x)`. -/
theorem served_on_arrival {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) {ρ : Request Page} (hρ : ρ ∈ input.requests)
    (ha : ρ.arrival = t) (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    (snapAt input i).x ρ.page = δ ∧
      (⟨t, (snapAt input i).x⟩ : Waypoint Page) ∈
        waypoints input (snapAt input i) (moveAt i h) := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext ⊢
  exact next_tick_served hnext hρ ha hρ'

/-- A request leaves the pending list (or is served on arrival) at a waypoint at or after its arrival with `x_p = δ`. -/
theorem served_of_removed {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending ∨
      (∃ t, moveAt i h = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t))
    (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    ∃ w ∈ waypoints input (snapAt input i) (moveAt i h),
      ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta := by
  rcases hρ with hρ | ⟨t, ht, hreq, ha⟩
  · obtain ⟨-, w, hw, hwt, hws⟩ := pending_removed hv h hρ hρ'
    exact ⟨w, hw, hwt ▸ (pending_spec hv hρ).2.1, hws⟩
  · obtain ⟨hx, hw⟩ := served_on_arrival hv h ht hreq ha hρ'
    exact ⟨_, hw, ha.le, hx⟩

/-! ### Structure of preemptive services and level loops -/

theorem lt_length_of_stage {l : ℕ} (hl : (snapAt input l).stage ≠ .idle) :
    l < (log input).length := by
  by_contra hge
  rw [snapAt_of_ge (by omega)] at hl
  have := (final_spec hv).2.2.1
  rw [snapAt_of_ge le_rfl] at this
  exact hl this

/-- Every preemptive service closes: an `openHole e` is followed by round trips of level `e` and then by a `closeHole e`. -/
theorem preempt_block {i : ℕ} (h : i < (log input).length) {e : ℤ}
    (hm : moveAt i h = .openHole e) :
    ∃ j, ∃ hj : j < (log input).length, i < j ∧ (∃ stop, moveAt j hj = .closeHole e stop) ∧
      ∀ l (hl : l < (log input).length), i < l → l < j → ∃ π, moveAt l hl = .trip e π := by
  classical
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨-, -, heq⟩ := next_openHole hnext
  have hst1 : (snapAt input (i + 1)).stage = .preempt e (snapAt input i).x := by rw [heq]
  let P : ℕ → Prop := fun l => i < l ∧
    ∀ hl : l < (log input).length, ∀ π, moveAt l hl ≠ .trip e π
  have hP : ∃ l, P l := ⟨(log input).length, h, fun hl => absurd hl (lt_irrefl _)⟩
  have hj : P (Nat.find hP) := Nat.find_spec hP
  have hmin : ∀ l < Nat.find hP, ¬ P l := fun l hl => Nat.find_min hP hl
  have hstage : ∀ l, i + 1 ≤ l → l ≤ Nat.find hP →
      (snapAt input l).stage = .preempt e (snapAt input i).x := by
    intro l hl1
    induction l, hl1 using Nat.le_induction with
    | base => intro _; exact hst1
    | succ l hl ih =>
      intro hl2
      have hnP := hmin l (by omega)
      simp only [P, not_and, not_forall, not_not] at hnP
      obtain ⟨hl', π, hπ⟩ := hnP (by omega)
      have hs := ih (by omega)
      rcases next_of_preempt hs (next_snapAt hv l hl') with ⟨π', -, hst'⟩ | ⟨stop, hm', -⟩
      · exact hst'
      · rw [hπ] at hm'; cases hm'
  have hjst := hstage (Nat.find hP) hj.1 le_rfl
  have hjlt : Nat.find hP < (log input).length :=
    lt_length_of_stage hv (by rw [hjst]; simp)
  refine ⟨Nat.find hP, hjlt, hj.1, ?_, ?_⟩
  · rcases next_of_preempt hjst (next_snapAt hv _ hjlt) with ⟨π, hm', -⟩ | ⟨stop, hm', -⟩
    · exact absurd hm' (hj.2 hjlt π)
    · exact ⟨stop, hm'⟩
  · intro l hl hil hlj
    have hnP := hmin l hlj
    simp only [P, not_and, not_forall, not_not] at hnP
    obtain ⟨hl', π, hπ⟩ := hnP hil
    exact ⟨π, hπ⟩

/-- Every round trip and close belongs to a preemptive service: going back from it, there are only round trips of the same level until its `openHole`. -/
theorem preempt_start {l : ℕ} (hl : l < (log input).length) {e : ℤ}
    (hm : (∃ π, moveAt l hl = .trip e π) ∨ (∃ stop, moveAt l hl = .closeHole e stop)) :
    ∃ i, ∃ hi : i < (log input).length, i < l ∧ moveAt i hi = .openHole e ∧
      ∀ l' (hl' : l' < (log input).length), i < l' → l' < l → ∃ π, moveAt l' hl' = .trip e π := by
  have key : ∀ l b, l ≤ (log input).length → (snapAt input l).stage = .preempt e b →
      ∃ i, ∃ hi : i < (log input).length, i < l ∧ moveAt i hi = .openHole e ∧
        ∀ l' (hl' : l' < (log input).length), i < l' → l' < l →
          ∃ π, moveAt l' hl' = .trip e π := by
    intro l
    induction l with
    | zero =>
      intro b _ hs
      rw [snapAt_zero hv] at hs
      simp [initialSnap] at hs
    | succ l ih =>
      intro b hl hs
      have hlt : l < (log input).length := by omega
      rcases next_to_preempt (next_snapAt hv l hlt) hs with hm | ⟨π, hm, hs'⟩
      · exact ⟨l, hlt, by omega, hm, fun l' _ h1 h2 => by omega⟩
      · obtain ⟨i, hi, hil, hio, htr⟩ := ih b hlt.le hs'
        refine ⟨i, hi, by omega, hio, fun l' hl' h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
        · exact htr l' hl' h1 h3
        · subst h3; exact ⟨π, hm⟩
  obtain ⟨b, hs⟩ : ∃ b, (snapAt input l).stage = .preempt e b := by
    rcases hm with ⟨π, hπ⟩ | ⟨stop, hst⟩
    · exact (trip_spec hv hl hπ).1
    · obtain ⟨b, hb, -⟩ := closeHole_spec hv hl hst
      exact ⟨b, hb⟩
  exact key l b hl.le hs

/-- No tick, advance or critical service happens at an entry whose stage is not idle. -/
theorem not_idle_moves {l : ℕ} (hl : l < (log input).length)
    (hs : (snapAt input l).stage ≠ .idle) :
    (∀ p, moveAt l hl ≠ .critical p) ∧ (∀ t, moveAt l hl ≠ .tick t) ∧
      (∀ t, moveAt l hl ≠ .advance t) := by
  refine ⟨fun p hp => hs (critical_spec hv hl hp).1, fun t ht => hs (tick_spec hv hl ht).1,
    fun t ht => hs (advance_spec hv hl ht).1⟩

/-- After a level-`e` examination at `l`, the level is dealt with at some `j ≥ l` by a `skip e` or a `closeHole e`, without critical services, ticks or advances. -/
theorem level_done {l : ℕ} {e : ℤ} (hl : (snapAt input l).stage = .examine e) :
    ∃ j, ∃ hj : j < (log input).length, l ≤ j ∧
      (moveAt j hj = .skip e ∨ ∃ stop, moveAt j hj = .closeHole e stop) ∧
      (snapAt input (j + 1)).stage = afterLevel input e ∧
      ∀ l' (hl' : l' < (log input).length), l ≤ l' → l' ≤ j →
        (∀ π, moveAt l' hl' ≠ .critical π) ∧ (∀ t, moveAt l' hl' ≠ .tick t) ∧
          (∀ t, moveAt l' hl' ≠ .advance t) := by
  have hlt : l < (log input).length := lt_length_of_stage hv (by rw [hl]; simp)
  rcases next_of_examine hl (next_snapAt hv l hlt) with ⟨hm, hst⟩ | ⟨hm, hst⟩
  · refine ⟨l, hlt, le_rfl, Or.inl hm, hst, fun l' hl' h1 h2 => ?_⟩
    obtain rfl : l' = l := by omega
    have : moveAt l' hl' = .skip e := hm
    rw [this]; simp
  · obtain ⟨j, hj, hlj, ⟨stop, hjm⟩, htr⟩ := preempt_block hv hlt hm
    have hjst : (snapAt input (j + 1)).stage = afterLevel input e := by
      obtain ⟨b, -, -, heq⟩ := closeHole_spec hv hj hjm
      rw [heq]
    refine ⟨j, hj, hlj.le, Or.inr ⟨stop, hjm⟩, hjst, fun l' hl' h1 h2 => ?_⟩
    rcases (show l' = l ∨ (l < l' ∧ l' < j) ∨ l' = j by omega) with h3 | h3 | h3
    · subst h3
      have : moveAt l' hl' = .openHole e := hm
      rw [this]; simp
    · obtain ⟨π, hπ⟩ := htr l' hl' h3.1 h3.2
      rw [hπ]; simp
    · subst h3
      have : moveAt l' hl' = .closeHole e stop := hjm
      rw [this]; simp

/-- The level loop after a critical service examines every level: each level `e` gets a later `skip e` or `closeHole e`, with no critical service, tick or advance in between. -/
theorem levelLoop_examines {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) {e : ℤ} (he₁ : minLevel input ≤ e)
    (he₂ : e ≤ maxLevel input) :
    ∃ j, ∃ hj : j < (log input).length, i < j ∧
      (moveAt j hj = .skip e ∨ ∃ stop, moveAt j hj = .closeHole e stop) ∧
      ∀ l (hl : l < (log input).length), i < l → l ≤ j →
        (∀ π, moveAt l hl ≠ .critical π) ∧ (∀ t, moveAt l hl ≠ .tick t) ∧
          (∀ t, moveAt l hl ≠ .advance t) := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨-, -, heq⟩ := next_critical hnext
  have hst1 : (snapAt input (i + 1)).stage = .examine (minLevel input) := by rw [heq]
  have key : ∀ e, minLevel input ≤ e → e ≤ maxLevel input →
      ∃ l, i < l ∧ (snapAt input l).stage = .examine e ∧
        ∀ l' (hl' : l' < (log input).length), i < l' → l' < l →
          (∀ π, moveAt l' hl' ≠ .critical π) ∧ (∀ t, moveAt l' hl' ≠ .tick t) ∧
            (∀ t, moveAt l' hl' ≠ .advance t) := by
    intro e he1
    induction e, he1 using Int.le_induction with
    | base => intro _; exact ⟨i + 1, by omega, hst1, fun l' _ h1 h2 => by omega⟩
    | succ e he ih =>
      intro he2
      obtain ⟨l, hil, hl, hq⟩ := ih (by omega)
      obtain ⟨j, hj, hlj, -, hjst, hq'⟩ := level_done hv hl
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [hjst]; simp [afterLevel, show e < maxLevel input by omega]
      · intro l' hl' h1 h2
        by_cases h3 : l' < l
        · exact hq l' hl' h1 h3
        · exact hq' l' hl' (by omega) (by omega)
  obtain ⟨l, hil, hl, hq⟩ := key e he₁ he₂
  obtain ⟨j, hj, hlj, hjm, -, hq'⟩ := level_done hv hl
  refine ⟨j, hj, by omega, hjm, fun l' hl' h1 h2 => ?_⟩
  by_cases h3 : l' < l
  · exact hq l' hl' h1 h3
  · exact hq' l' hl' (by omega) h2

end

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Path` -/
section

/-!
# Costs of concatenated paths

`pathFrom d y W` is the cost of the polygonal path from the state `y` through the waypoints of `W`, where `d a b` is the cost of the segment from `a` to `b`. It is additive under concatenation; the fractional fetch cost of a schedule is an instance.
-/

set_option linter.unusedSectionVars false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page]

/-- The segment cost of the fetch cost. -/
noncomputable def dFetch (input : Instance Page) (a b : Page → ℝ) : ℝ :=
  ∑ i, w i * max 0 (a i - b i)

theorem dFetch_self (input : Instance Page) (a : Page → ℝ) : dFetch input a a = 0 := by
  simp [dFetch]

/-- The cost of the path from `y` through the waypoints. -/
noncomputable def pathFrom (d : (Page → ℝ) → (Page → ℝ) → ℝ) :
    (Page → ℝ) → List (Waypoint Page) → ℝ
  | _, [] => 0
  | y, a :: rest => d y a.state + pathFrom d a.state rest

/-- The state at the end of the path from `y` through the waypoints. -/
def lastState : (Page → ℝ) → List (Waypoint Page) → Page → ℝ
  | y, [] => y
  | _, a :: rest => lastState a.state rest

@[simp] theorem pathFrom_nil (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ) :
    pathFrom d y [] = 0 := rfl

@[simp] theorem pathFrom_cons (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ)
    (a : Waypoint Page) (rest : List (Waypoint Page)) :
    pathFrom d y (a :: rest) = d y a.state + pathFrom d a.state rest := rfl

@[simp] theorem lastState_nil (y : Page → ℝ) : lastState y ([] : List (Waypoint Page)) = y := rfl

@[simp] theorem lastState_cons (y : Page → ℝ) (a : Waypoint Page) (rest : List (Waypoint Page)) :
    lastState y (a :: rest) = lastState a.state rest := rfl

theorem pathFrom_append (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ)
    (A B : List (Waypoint Page)) :
    pathFrom d y (A ++ B) = pathFrom d y A + pathFrom d (lastState y A) B := by
  induction A generalizing y with
  | nil => simp
  | cons a A ih => simp [ih]; ring

theorem lastState_append (y : Page → ℝ) (A B : List (Waypoint Page)) :
    lastState y (A ++ B) = lastState (lastState y A) B := by
  induction A generalizing y with
  | nil => simp
  | cons a A ih => simp [ih]

theorem fetchCost_eq_pathFrom (input : Instance Page) (a : Waypoint Page)
    (rest : List (Waypoint Page)) :
    FracSchedule.fetchCost input (a :: rest) = pathFrom (dFetch input) a.state rest := by
  induction rest generalizing a with
  | nil => simp [FracSchedule.fetchCost]
  | cons b rest ih => simp [FracSchedule.fetchCost, ih, dFetch]

theorem fetchCost_eq_pathFrom' (input : Instance Page) (y : Page → ℝ) (W : List (Waypoint Page))
    (hW : ∀ a ∈ W.head?, a.state = y) :
    FracSchedule.fetchCost input W = pathFrom (dFetch input) y W := by
  cases W with
  | nil => simp [FracSchedule.fetchCost]
  | cons a rest =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hW
    rw [fetchCost_eq_pathFrom, pathFrom_cons, hW, dFetch_self, zero_add]

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Steps` -/
section

/-!
# Helper facts about the run

The log as a list of `(snapAt i, moveAt i)`, the output as the concatenation of the entries' waypoints (`wpAt`), its fetch cost as a sum over the entries (`pathFrom_output`, `fetchCost_output`), the first move, the range of examined levels, and fractional states along the run.

The path costs `pathFrom`, `lastState`, `dFetch` are those of `Run/Path.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage IsRest IsFrac
  restMass pathFrom lastState dFetch)

noncomputable section

variable {input : Instance Page}

theorem sum_update_eq {ι : Type*} [DecidableEq ι] {S : Finset ι} {a : ι} (ha : a ∈ S)
    (f : ι → ℝ) (v : ℝ) : ∑ x ∈ S, Function.update f a v x = ∑ x ∈ S, f x - f a + v := by
  rw [Finset.sum_update_of_mem ha, ← Finset.sum_sdiff (Finset.singleton_subset_iff.2 ha) (f := f),
    Finset.sum_singleton]
  ring

theorem log_getElem (i : ℕ) (h : i < (log input).length) :
    (log input)[i] = (snapAt input i, moveAt i h) := by
  simp [snapAt, h, moveAt]

theorem snapAt_of_ge_len {i : ℕ} (h : (log input).length ≤ i) :
    snapAt input i = snapAt input (log input).length := by
  simp [snapAt, not_lt.2 h]

/-- The waypoints of entry `i` (empty past the end). -/
def wpAt (input : Instance Page) (i : ℕ) : List (Waypoint Page) :=
  if h : i < (log input).length then waypoints input (snapAt input i) (moveAt i h) else []

theorem wpAt_of_lt {i : ℕ} (h : i < (log input).length) :
    wpAt input i = waypoints input (snapAt input i) (moveAt i h) := by
  simp [wpAt, h]

/-- The output of `PMD` is the concatenation of the waypoints of the log entries. -/
theorem output_eq (hv : input.Valid) :
    preemptiveMirrorDescent input = (log input).flatMap fun e => waypoints input e.1 e.2 :=
  rfl

theorem mem_output_iff (hv : input.Valid) {w : Waypoint Page} :
    w ∈ preemptiveMirrorDescent input ↔ ∃ i, ∃ _ : i < (log input).length, w ∈ wpAt input i := by
  simp only [preemptiveMirrorDescent, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hw⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    rw [log_getElem i hi] at hw
    exact ⟨i, hi, by simpa [wpAt, hi] using hw⟩
  · rintro ⟨i, hi, hw⟩
    refine ⟨_, List.getElem_mem hi, ?_⟩
    rw [log_getElem i hi]
    simpa [wpAt, hi] using hw

theorem flatMap_take (m : ℕ) (hm : m ≤ (log input).length) :
    ((log input).take (m + 1)).flatMap (fun e => waypoints input e.1 e.2) =
      ((log input).take m).flatMap (fun e => waypoints input e.1 e.2) ++ wpAt input m := by
  by_cases h : m < (log input).length
  · rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem h, log_getElem m h]
    simp [wpAt, h]
  · have hm' : m = (log input).length := le_antisymm hm (not_lt.1 h)
    subst hm'
    simp [wpAt, List.take_of_length_le (Nat.le_succ _)]

/-- Summing along the chain: if each entry ends in the state before the next, the cost of the output from the initial state is the sum of the entries' costs. -/
theorem pathFrom_take (d : (Page → ℝ) → (Page → ℝ) → ℝ)
    (hlast : ∀ i, i < (log input).length →
      lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x)
    (m : ℕ) (hm : m ≤ (log input).length) :
    pathFrom d (snapAt input 0).x
        (((log input).take m).flatMap (fun e => waypoints input e.1 e.2)) =
      ∑ i ∈ Finset.range m, pathFrom d (snapAt input i).x (wpAt input i) ∧
    lastState (snapAt input 0).x
        (((log input).take m).flatMap (fun e => waypoints input e.1 e.2)) =
      (snapAt input m).x := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [flatMap_take m (by omega), PagingWithDelay.PMD.pathFrom_append,
      PagingWithDelay.PMD.lastState_append, ih2, ih1, Finset.sum_range_succ]
    exact ⟨rfl, hlast m (by omega)⟩

theorem pathFrom_output (d : (Page → ℝ) → (Page → ℝ) → ℝ)
    (hlast : ∀ i, i < (log input).length →
      lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x) :
    pathFrom d (snapAt input 0).x
        ((log input).flatMap (fun e => waypoints input e.1 e.2)) =
      ∑ i ∈ Finset.range (log input).length,
        pathFrom d (snapAt input i).x (wpAt input i) := by
  have := (pathFrom_take d hlast (log input).length le_rfl).1
  rwa [List.take_length] at this

/-- The levels examined or in a preemptive service lie in `[minLevel, maxLevel]`. -/
def StageOK (input : Instance Page) : Stage Page → Prop
  | .idle => True
  | .examine e => minLevel input ≤ e ∧ e ≤ maxLevel input
  | .preempt e _ => minLevel input ≤ e ∧ e ≤ maxLevel input

theorem stageOK_afterLevel {e : ℤ} (he : minLevel input ≤ e ∧ e ≤ maxLevel input) :
    StageOK input (afterLevel input e) := by
  unfold afterLevel
  split_ifs with h
  · exact ⟨by omega, by omega⟩
  · trivial

theorem baseState_of_preempt {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) : baseState (snapAt input i) = b := by
  simp [baseState, hs]

section

variable (hv : input.Valid)
include hv

/-- The first move is a tick (no request is pending initially). -/
theorem first_tick (h : 0 < (log input).length) :
    ∃ t, moveAt 0 h = .tick t := by
  have hn := next_snapAt hv 0 h
  have hinv := inv_snapAt hv 0
  rw [snapAt_zero hv] at hn hinv
  generalize hm : moveAt 0 h = m at hn
  cases m with
  | tick t => exact ⟨t, rfl⟩
  | advance t =>
    obtain ⟨-, -, hadv, -⟩ := next_advance hn
    obtain ⟨τ, -, p, hp⟩ := hadv.1
    obtain ⟨ρ, hρ, -⟩ :=
      exists_pending_of_triggered (triggered_of_triggerCond hp) (hinv.claims p) (hv.weight_pos p)
    simp [initialSnap] at hρ
  | critical p =>
    obtain ⟨-, hp, -⟩ := next_critical hn
    obtain ⟨ρ, hρ, -⟩ := hinv.exists_pending_of_triggerPage hv hp
    simp [initialSnap] at hρ
  | skip e => obtain ⟨hs, -⟩ := next_skip hn; simp [initialSnap] at hs
  | openHole e => obtain ⟨hs, -⟩ := next_openHole hn; simp [initialSnap] at hs
  | trip e π => obtain ⟨⟨b, hs⟩, -⟩ := next_trip hn; simp [initialSnap] at hs
  | closeHole e stop => obtain ⟨b, hs, -⟩ := next_closeHole hn; simp [initialSnap] at hs

/-- The head of the output is the initial state. -/
theorem output_head :
    ∀ a ∈ ((log input).flatMap (fun e => waypoints input e.1 e.2)).head?,
      a.state = (snapAt input 0).x := by
  intro a ha
  rcases hl : log input with _ | ⟨e0, tl⟩
  · simp [hl] at ha
  · have h0 : 0 < (log input).length := by simp [hl]
    obtain ⟨t, ht⟩ := first_tick hv h0
    have he0 : e0 = (snapAt input 0, moveAt 0 h0) := by
      rw [← log_getElem 0 h0]; simp [hl]
    rw [hl, he0, ht] at ha
    simp [waypoints] at ha
    rw [← ha]

/-- Every entry ends in the state before the next one. -/
theorem lastState_wpAt (i : ℕ) (h : i < (log input).length) :
    lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x := by
  rw [wpAt_of_lt h]
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · rw [(tick_spec hv h hm).2.2.2.2]; simp [waypoints]
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]; simp [waypoints]
  · rw [(critical_spec hv h hm).2.2]; simp [waypoints]
  · rw [(skip_spec hv h hm).2.2]; simp [waypoints]
  · rw [(openHole_spec hv h hm).2.2]; simp [waypoints]
  · rw [(trip_spec hv h hm).2.2.2]; simp [waypoints]
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    rw [he]; simp [waypoints, hs]

/-- The fetch cost of the output is the sum over the log entries of the fetch costs of their waypoint paths. -/
theorem fetchCost_output :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) =
      ∑ i ∈ Finset.range (log input).length,
        pathFrom (dFetch input) (snapAt input i).x (wpAt input i) := by
  rw [output_eq hv,
    PagingWithDelay.PMD.fetchCost_eq_pathFrom' input (snapAt input 0).x _
      (output_head hv)]
  exact pathFrom_output _ (lastState_wpAt hv)

theorem stageOK (i : ℕ) : StageOK input (snapAt input i).stage := by
  induction i with
  | zero => rw [snapAt_zero hv]; trivial
  | succ i ih =>
    by_cases h : i < (log input).length
    · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
      · rw [(tick_spec hv h hm).2.2.2.2]; exact ih
      · rw [(advance_spec hv h hm).2.2.2.2.2.2]; exact ih
      · rw [(critical_spec hv h hm).2.2]
        exact ⟨le_rfl, PagingWithDelay.PMD.minLevel_le_maxLevel hv⟩
      · obtain ⟨hs, -, he⟩ := skip_spec hv h hm
        rw [he]; rw [hs] at ih; exact stageOK_afterLevel ih
      · obtain ⟨hs, -, he⟩ := openHole_spec hv h hm
        rw [he]; rw [hs] at ih; exact ih
      · rw [(trip_spec hv h hm).2.2.2]; exact ih
      · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
        rw [he]; rw [hs] at ih; exact stageOK_afterLevel ih
    · rw [snapAt_of_ge_len (by omega)]
      rw [snapAt_of_ge_len (by omega)] at ih
      exact ih

/-- Every state of the run is fractional with missing mass at least `n - k`. -/
theorem x_frac (i : ℕ) :
    IsFrac input (snapAt input i).x ∧ restMass input ≤ ∑ j, (snapAt input i).x j := by
  have hvb := hv
  by_cases hs : ∃ e b, (snapAt input i).stage = .preempt e b
  · obtain ⟨e, b, hs⟩ := hs
    obtain ⟨hx, hcond⟩ := x_eq_hole hv hs
    have hb := baseState_isRest hv i
    rw [baseState_of_preempt hs] at hb
    rw [hx]
    refine ⟨PagingWithDelay.PMD.hole_isFrac hvb hb.1 e, ?_⟩
    rw [PagingWithDelay.PMD.sum_hole hvb hb.1 e hcond, hb.2]
    linarith [Instance.delta_lt_one hv]
  · push_neg at hs
    rw [x_eq_baseState hv hs]
    exact ⟨(baseState_isRest hv i).1, (baseState_isRest hv i).2.ge⟩

/-- Every waypoint of entry `i` is at the time of the entry and is a fractional state with missing mass at least `n - k`. -/
theorem wp_spec (i : ℕ) (h : i < (log input).length) :
    ∀ w ∈ wpAt input i, w.time = entryTime input i ∧ IsFrac input w.state ∧
      restMass input ≤ ∑ j, w.state j := by
  intro w hw
  have hfr := x_frac hv
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    exact ⟨(entryTime_tick hv h hm).symm, hfr i⟩
  · simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    exact ⟨(entryTime_advance hv h hm).1.symm, hfr i⟩
  · obtain ⟨-, -, he⟩ := critical_spec hv h hm
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    have hx1 : (snapAt input (i + 1)).x =
        criticalState input (snapAt input i).x p := by rw [he]
    refine ⟨ht.symm, ?_⟩
    try dsimp only
    rw [← hx1]; exact hfr (i + 1)
  · simp [wpAt, dif_pos h, hm, waypoints] at hw
  · obtain ⟨-, -, he⟩ := openHole_spec hv h hm
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    have hx1 : (snapAt input (i + 1)).x = hole input (snapAt input i).x e := by rw [he]
    refine ⟨ht.symm, ?_⟩
    try dsimp only
    rw [← hx1]; exact hfr (i + 1)
  · obtain ⟨⟨b, hs⟩, -, -, -⟩ := trip_spec hv h hm
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · subst hw
      refine ⟨ht.symm, ?_, ?_⟩
      · intro j
        by_cases hj : j = π.page
        · subst hj
          simp only [Function.update_self]
          exact ⟨le_rfl, (Instance.delta_lt_one hv).le⟩
        · simp only [Function.update_of_ne hj]
          exact (hfr i).1 j
      · obtain ⟨hx, hcond⟩ := x_eq_hole hv hs
        have hb := baseState_isRest hv i
        rw [baseState_of_preempt hs] at hb
        have hsum : ∑ j, (snapAt input i).x j = restMass input + (1 - input.delta) := by
          rw [hx, PagingWithDelay.PMD.sum_hole hv hb.1 e hcond, hb.2]
        have hp := ((hfr i).1 π.page).2
        try dsimp only
        rw [sum_update_eq (Finset.mem_univ _), hsum]
        linarith
    · subst hw
      exact ⟨ht.symm, hfr i⟩
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, waypoints, hs, List.mem_singleton] at hw
    subst hw
    have hx1 : (snapAt input (i + 1)).x = b := by rw [he]
    refine ⟨ht.symm, ?_⟩
    try dsimp only
    rw [← hx1]; exact hfr (i + 1)

/-- While a request stays pending, no waypoint has its page at `δ`: if `ρ` is pending after entry `i`, every waypoint of entry `i` has `x_p > δ`. Hence a request is served (`FracSchedule.serviceTime`) exactly at the entry that removes it from the pending list (or at its arrival tick, if it never becomes pending). -/
theorem delta_lt_wp_of_pending_succ {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (i + 1)).pending) :
    ∀ w ∈ wpAt input i, input.delta < w.state ρ.page := by
  intro w hw
  have hfr := x_frac hv
  have hnext : input.delta < (snapAt input (i + 1)).x ρ.page := delta_lt_of_pending hv hρ
  rw [wpAt_of_lt h] at hw
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> rw [hm] at hw
  · have he := (tick_spec hv h hm).2.2.2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hρ
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    exact lt_of_le_of_ne ((hfr i).1 ρ.page).1 (Ne.symm hρ.2)
  · have he := (advance_spec hv h hm).2.2.2.2.2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · have he := (critical_spec hv h hm).2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · simp [waypoints] at hw
  · have he := (openHole_spec hv h hm).2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · have he := (trip_spec hv h hm).2.2.2
    have hρ' := hρ
    rw [he] at hρ'
    simp only [List.mem_filter, decide_eq_true_eq] at hρ'
    have hx : input.delta < (snapAt input i).x ρ.page := delta_lt_of_pending hv hρ'.1
    simp only [waypoints, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · subst hw
      simp only [Function.update_of_ne hρ'.2]
      exact hx
    · subst hw; exact hx
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    simp only [waypoints, hs, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext

end

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Feasible` -/
section

/-!
# `PMD` is feasible (`lem:inv`)

Every waypoint is a fractional state with missing mass at least `n - k`, the waypoints are chronological, and every request is served: on arrival (`x_p = δ` at the tick), or later by a visit of its page, which records a waypoint with `x_p = δ`. At the end nothing is pending, since a pending request would eventually trigger (`lem:inv`(b)).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- A property that holds at `a` and fails at `b ≥ a` is lost at some step in between. -/
theorem exists_drop (P : ℕ → Prop) {a b : ℕ} (ha : P a) (hb : ¬ P b) (hab : a ≤ b) :
    ∃ j, a ≤ j ∧ j < b ∧ P j ∧ ¬ P (j + 1) := by
  induction b with
  | zero => exact absurd (by rwa [Nat.le_zero.1 hab] at ha) hb
  | succ b ih =>
    by_cases hP : P b
    · refine ⟨b, ?_, by omega, hP, hb⟩
      rcases Nat.lt_or_ge b a with h | h
      · exact absurd (by rwa [show a = b + 1 by omega] at ha) hb
      · exact h
    · have hab' : a ≤ b := by
        rcases Nat.lt_or_ge b a with h | h
        · exact absurd (by rwa [show a = b + 1 by omega] at ha) hb
        · exact h
      obtain ⟨j, h1, h2, h3, h4⟩ := ih hP hab'
      exact ⟨j, h1, by omega, h3, h4⟩

section

variable {input : Instance Page} (hv : input.Valid)
include hv

/-- Every request is served by some log entry `j`: a waypoint of `j` at or after the arrival has `x_p = δ` (the tick of its arrival, or the visit that removes it from the pending list). -/
theorem exists_serving_entry {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ j, ∃ hj : j < (log input).length, ∃ w ∈ wpAt input j,
      ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta := by
  obtain ⟨i0, h0, ht⟩ := exists_tick_arrival hv hρ
  have key : ∃ j, ∃ hj : j < (log input).length,
      (ρ ∈ (snapAt input j).pending ∨
        (∃ t, moveAt j hj = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t)) ∧
      ρ ∉ (snapAt input (j + 1)).pending := by
    by_cases hin : ρ ∈ (snapAt input (i0 + 1)).pending
    · have hfin : ρ ∉ (snapAt input (log input).length).pending := by
        rw [(final_spec hv).2.1]; simp
      obtain ⟨j, -, hj2, hPj, hPj1⟩ :=
        exists_drop (fun m => ρ ∈ (snapAt input m).pending) hin hfin (by omega)
      exact ⟨j, hj2, Or.inl hPj, hPj1⟩
    · exact ⟨i0, h0, Or.inr ⟨_, ht, hρ, rfl⟩, hin⟩
  obtain ⟨j, hj, hr1, hr2⟩ := key
  obtain ⟨w, hw, hw'⟩ := served_of_removed hv hj hr1 hr2
  exact ⟨j, hj, w, by rw [wpAt_of_lt hj]; exact hw, hw'⟩

/-- **When a request is served.** Let `i₀` be the tick of the arrival of `ρ`. Then there is an entry `j ≥ i₀` such that `ρ` is pending before every entry `l` with `i₀ < l ≤ j` and not after `j`, and the service time of `ρ` is `entryTime j`. If `j = i₀`, `ρ` is served on arrival (`x_p = δ` at the tick); otherwise entry `j` is a visit of its page (`pending_removed`). -/
theorem serviceTime_spec {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ i₀ j, ∃ h₀ : i₀ < (log input).length, ∃ hj : j < (log input).length,
      moveAt i₀ h₀ = .tick ρ.arrival ∧ i₀ ≤ j ∧
      (∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending) ∧
      ρ ∉ (snapAt input (j + 1)).pending ∧
      FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ = entryTime input j := by
  classical
  obtain ⟨i₀, h₀, ht⟩ := exists_tick_arrival hv hρ
  let Q : ℕ → Prop := fun m => i₀ ≤ m ∧ ρ ∉ (snapAt input (m + 1)).pending
  have hQ : ∃ m, Q m := by
    refine ⟨(log input).length - 1, by omega, ?_⟩
    rw [show (log input).length - 1 + 1 = (log input).length by omega, (final_spec hv).2.1]
    simp
  obtain ⟨j, hjQ, hjmin⟩ : ∃ j, Q j ∧ ∀ m < j, ¬ Q m :=
    ⟨Nat.find hQ, Nat.find_spec hQ, fun m hm => Nat.find_min hQ hm⟩
  have hjlt : j < (log input).length := by
    by_contra hge
    apply hjmin ((log input).length - 1) (by omega)
    refine ⟨by omega, ?_⟩
    rw [show (log input).length - 1 + 1 = (log input).length by omega, (final_spec hv).2.1]
    simp
  have hpend : ∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending := by
    intro l h1 h2
    have := hjmin (l - 1) (by omega)
    simp only [Q, not_and, not_not] at this
    have h := this (by omega)
    rwa [show l - 1 + 1 = l by omega] at h
  refine ⟨i₀, j, h₀, hjlt, ht, hjQ.1, hpend, hjQ.2, ?_⟩
  have hr1 : ρ ∈ (snapAt input j).pending ∨
      (∃ t, moveAt j hjlt = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t) := by
    rcases eq_or_lt_of_le hjQ.1 with h | h
    · right
      subst h
      exact ⟨_, ht, hρ, rfl⟩
    · exact Or.inl (hpend j h le_rfl)
  obtain ⟨w, hw, hwa, hws⟩ := served_of_removed hv hjlt hr1 hjQ.2
  have hwt : w.time = entryTime input j :=
    (wp_spec hv j hjlt w (by rw [wpAt_of_lt hjlt]; exact hw)).1
  unfold FracSchedule.serviceTime
  apply IsLeast.csInf_eq
  refine ⟨⟨w, (mem_output_iff hv).mpr ⟨j, hjlt, by rw [wpAt_of_lt hjlt]; exact hw⟩, hwa, hws,
    hwt⟩, ?_⟩
  rintro s ⟨w', hw', hwa', hws', rfl⟩
  obtain ⟨i, hi, hwi⟩ := (mem_output_iff hv).mp hw'
  have hwt' : w'.time = entryTime input i := (wp_spec hv i hi w' hwi).1
  rw [hwt']
  by_cases hji : j ≤ i
  · exact entryTime_mono hv hji
  · exfalso
    by_cases hii : i < i₀
    · have := entryTime_lt_of_tick hv h₀ ht hii
      rw [hwt'] at hwa'
      linarith
    · have hp := hpend (i + 1) (by omega) (by omega)
      have := delta_lt_wp_of_pending_succ hv hi hp w' hwi
      rw [hws'] at this
      exact lt_irrefl _ this

end

theorem preemptiveMirrorDescent_feasible :
    (preemptiveMirrorDescent : FracAlgorithm Page).Feasible := by
  intro input
  have hv := input.valid
  constructor
  · show List.Pairwise _ ((log input).flatMap _)
    rw [List.pairwise_flatMap]
    constructor
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [log_getElem i hi]
      have hs := wp_spec hv i hi
      simp only [wpAt, dif_pos hi] at hs
      apply List.pairwise_of_forall_mem_list
      intro a ha b hb
      rw [(hs a ha).1, (hs b hb).1]
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [log_getElem i hi, log_getElem j hj]
      intro a ha b hb
      have hsi := wp_spec hv i hi
      have hsj := wp_spec hv j hj
      simp only [wpAt, dif_pos hi, dif_pos hj] at hsi hsj
      rw [(hsi a ha).1, (hsj b hb).1]
      exact entryTime_mono hv hij.le
  · intro w hw
    obtain ⟨i, hi, hw⟩ := (mem_output_iff hv).mp hw
    exact (wp_spec hv i hi w hw).2.1
  · intro w hw
    obtain ⟨i, hi, hw⟩ := (mem_output_iff hv).mp hw
    exact (wp_spec hv i hi w hw).2.2
  · intro ρ hρ
    obtain ⟨j, hj, w, hw, hw'⟩ := exists_serving_entry hv hρ
    exact ⟨w, (mem_output_iff hv).mpr ⟨j, hj, hw⟩, hw'⟩

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Opt` -/
section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The comparator (the lazy optimum of `sec:problem`)

The analysis compares against an arbitrary feasible schedule `S` with service times `σ`, which serves every request `ρ` in the window `[a_ρ, σ ρ]` (`FeasibleBy`). This file collects the facts about `S` that the analysis uses:
* the lazy optimum in swap form (`exists_swapForm`): `S` can be replaced, with the same windows and no larger fetch cost, by a schedule in which every step evicts one page and fetches another;
* its cache at a time (`cacheAt`), its evictions (`obs:evictions`), the lightest weights (`lem:lightest`), quiet windows, the last eviction of a page (the comparator side of `lem:miss` and `lem:chargeable`), and its periods;
* delay costs of groups of requests: `delayCostOn input σ I` is the delay cost of the requests with index in `I` (index sets, since requests may be duplicated in the list); pairwise disjoint groups sum to at most the total delay cost `totalDelay input σ`.
-/

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

namespace Schedule

/-- `σ` assigns service times: the page of every request `ρ` is cached by `S` at time `σ ρ ≥ a_ρ`. The analysis holds for every such `σ`; the first service times are one choice (`serviceTimes_serviceTime`). -/
def ServiceTimes (input : Instance Page) (S : Schedule Page) (σ : Request Page → ℝ) : Prop :=
  ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ ∧ CachedAt input S ρ.page (σ ρ)

/-- The cost of `S` with service times `σ`: its fetch cost plus the delay cost `∑_ρ d_ρ(σ ρ - a_ρ)`. -/
noncomputable def costWith (input : Instance Page) (S : Schedule Page)
    (σ : Request Page → ℝ) : ℝ :=
  fetchCost input S + (input.requests.map fun ρ => ρ.delay (σ ρ - ρ.arrival)).sum

theorem cost_eq_costWith (input : Instance Page) (S : Schedule Page) :
    S.cost input = S.costWith input (S.serviceTime input) := rfl

/-- The times at which a page is cached form a closed set. -/
theorem isClosed_cachedAt (input : Instance Page) (S : Schedule Page) (p : Page) :
    IsClosed {s | CachedAt input S p s} := by
  have hopt : ∀ o : Option (Step Page), IsClosed {s : ℝ | ∀ step ∈ o, s ≤ step.time} := by
    intro o
    cases o with
    | none => simp
    | some st =>
      have e : {s : ℝ | ∀ step ∈ some st, s ≤ step.time} = Set.Iic st.time := by
        ext s; simp
      rw [e]; exact isClosed_Iic
  have h : {s | CachedAt input S p s} =
      ({s | p ∈ input.initialCache} ∩ {s | ∀ step ∈ S.head?, s ≤ step.time}) ∪
        ⋃ j : Fin S.length, ({s | S[j].time ≤ s} ∩ {s | ∀ step ∈ S[(j : ℕ) + 1]?, s ≤ step.time} ∩
          {s | p ∈ S[j].cache}) := by
    ext s
    simp only [CachedAt, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro (h | ⟨j, hj, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨j, hj⟩, ⟨h1, h2⟩, h3⟩
    · rintro (h | ⟨j, ⟨h1, h2⟩, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, j.2, h1, h2, h3⟩
  rw [h]
  refine IsClosed.union ((isClosed_const).inter (hopt _)) (isClosed_iUnion_of_finite fun j => ?_)
  exact ((isClosed_Ici).inter (hopt _)).inter isClosed_const

/-- The first service times of a feasible schedule are service times: the infimum is attained. -/
theorem serviceTimes_serviceTime {input : Instance Page} {S : Schedule Page}
    (hF : S.Feasible input) : S.ServiceTimes input (S.serviceTime input) := by
  intro ρ hρ
  have hne : {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ}.Nonempty := hF.serves ρ hρ
  have hcl : IsClosed {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ} :=
    (isClosed_Ici (a := ρ.arrival)).inter (isClosed_cachedAt input S ρ.page)
  exact hcl.csInf_mem hne ⟨ρ.arrival, fun _ h => h.1⟩

/-- A request is served no later than any time after its arrival at which its page is cached. -/
theorem serviceTime_le {input : Instance Page} {S : Schedule Page} {ρ : Request Page} {s : ℝ}
    (hs : ρ.arrival ≤ s) (hc : CachedAt input S ρ.page s) : S.serviceTime input ρ ≤ s :=
  csInf_le ⟨ρ.arrival, fun _ h => h.1⟩ ⟨hs, hc⟩

/-- A request is served after its arrival (if it is served at all). -/
theorem arrival_le_serviceTime {input : Instance Page} {S : Schedule Page} {ρ : Request Page}
    (hne : ∃ s, ρ.arrival ≤ s ∧ CachedAt input S ρ.page s) :
    ρ.arrival ≤ S.serviceTime input ρ :=
  le_csInf hne fun _ h => h.1

variable {input : Instance Page} {σ : Request Page → ℝ}

theorem ServiceTimes.arrival_le {S : Schedule Page} (hσ : S.ServiceTimes input σ) :
    ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ := fun ρ hρ => (hσ ρ hρ).1

/-! ## Serving within the windows `[a_ρ, σ ρ]` -/

/-- `S` is feasible and serves every request `ρ` in the window `[a_ρ, σ ρ]`: its page is cached at some time `s` with `a_ρ ≤ s ≤ σ ρ`. -/
structure FeasibleBy (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page) :
    Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  capacity : ∀ step ∈ S, step.cache.card ≤ input.cacheSize
  serves : ∀ ρ ∈ input.requests, ∃ s, ρ.arrival ≤ s ∧ s ≤ σ ρ ∧ CachedAt input S ρ.page s

/-- `S` has served `ρ` by time `t`: its page is cached at some time `s` with `a_ρ ≤ s ≤ σ ρ` and `s ≤ t`. -/
def ServedBy (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page)
    (ρ : Request Page) (t : ℝ) : Prop :=
  ∃ s, ρ.arrival ≤ s ∧ s ≤ σ ρ ∧ s ≤ t ∧ CachedAt input S ρ.page s

/-- A feasible schedule with service times `σ` serves every request in its window `[a_ρ, σ ρ]`. -/
theorem Feasible.feasibleBy {S : Schedule Page} (hF : S.Feasible input)
    (hσ : S.ServiceTimes input σ) : S.FeasibleBy input σ where
  chronological := hF.chronological
  capacity := hF.capacity
  serves ρ hρ := ⟨σ ρ, (hσ ρ hρ).1, le_rfl, (hσ ρ hρ).2⟩

/-! ## The swap normal form: the construction -/

/-!
Given a feasible schedule `S`, we build `S'` along the steps of `S`, keeping a cache `C'` of exactly `k` pages that contains the current cache of `S`. At a step of `S` to the cache `C_new`, for each `p ∈ C_new \ C'` we evict some page of `C' \ C_new` and fetch `p` (a swap step at the same time). The facts are proved for recursive notions (`lastCache`, `Present`, `SwapFrom`) and then translated to the index-based ones.
-/

namespace NF

/-- The cache after the steps of `l`, starting from `C`. -/
def lastCache : Finset Page → Schedule Page → Finset Page
  | C, [] => C
  | _, st :: rest => lastCache st.cache rest

/-- `X` is a cache present at time `s` in the schedule `l` started from `C`. -/
def Present (s : ℝ) : Finset Page → Schedule Page → Finset Page → Prop
  | C, [], X => X = C
  | C, st :: rest, X => (s ≤ st.time ∧ X = C) ∨ (st.time ≤ s ∧ Present s st.cache rest X)

/-- Every step of `l` (started from `C`) is a swap. -/
def SwapFrom : Finset Page → Schedule Page → Prop
  | _, [] => True
  | C, st :: rest =>
      (∃ p q, p ∉ C ∧ q ∈ C ∧ st.cache = insert p (C.erase q)) ∧ SwapFrom st.cache rest

/-- One round: fetch the pages of `ps` one by one into `C`, each time evicting a page of `C \ Cnew`. -/
noncomputable def roundL (t : ℝ) (Cnew : Finset Page) : Finset Page → List Page → Schedule Page
  | _, [] => []
  | C, p :: ps =>
    if h : p ∉ C ∧ (C \ Cnew).Nonempty then
      ⟨t, insert p (C.erase h.2.choose)⟩ :: roundL t Cnew (insert p (C.erase h.2.choose)) ps
    else roundL t Cnew C ps

/-- The round for the step `st` of `S`, from the cache `C` of `S'`. -/
noncomputable def round (st : Step Page) (C : Finset Page) : Schedule Page :=
  roundL st.time st.cache C (st.cache \ C).toList

/-- The swap-form schedule. -/
noncomputable def build : Finset Page → Schedule Page → Schedule Page
  | _, [] => []
  | C, st :: rest => round st C ++ build (lastCache C (round st C)) rest

/-! ### Generic facts -/

theorem costFrom_append (w : Page → ℝ) (C : Finset Page) (l₁ l₂ : Schedule Page) :
    costFrom w C (l₁ ++ l₂) = costFrom w C l₁ + costFrom w (lastCache C l₁) l₂ := by
  induction l₁ generalizing C with
  | nil => simp [costFrom, lastCache]
  | cons st rest ih => simp only [List.cons_append, costFrom, lastCache, ih]; ring

theorem swapFrom_append (C : Finset Page) (l₁ l₂ : Schedule Page) :
    SwapFrom C (l₁ ++ l₂) ↔ SwapFrom C l₁ ∧ SwapFrom (lastCache C l₁) l₂ := by
  induction l₁ generalizing C with
  | nil => simp [SwapFrom, lastCache]
  | cons st rest ih => simp only [List.cons_append, SwapFrom, lastCache, ih, and_assoc]

theorem lastCache_card (n : ℕ) (C : Finset Page) (l : Schedule Page) (hC : C.card = n)
    (hl : ∀ x ∈ l, x.cache.card = n) : (lastCache C l).card = n := by
  induction l generalizing C with
  | nil => exact hC
  | cons st rest ih =>
    exact ih st.cache (hl st (by simp)) (fun x hx => hl x (by simp [hx]))

theorem present_self {s : ℝ} (C : Finset Page) (l : Schedule Page)
    (h : ∀ st ∈ l, s ≤ st.time) : Present s C l C := by
  cases l with
  | nil => rfl
  | cons st rest => exact Or.inl ⟨h st (by simp), rfl⟩

theorem present_append {s : ℝ} (C : Finset Page) (l₁ l₂ : Schedule Page) (X : Finset Page)
    (h₁ : ∀ st ∈ l₁, st.time ≤ s) (h : Present s (lastCache C l₁) l₂ X) :
    Present s C (l₁ ++ l₂) X := by
  induction l₁ generalizing C with
  | nil => exact h
  | cons st rest ih =>
    exact Or.inr ⟨h₁ st (by simp), ih st.cache (fun x hx => h₁ x (by simp [hx])) h⟩

theorem idx_of_present {s : ℝ} (C : Finset Page) (l : Schedule Page) (X : Finset Page)
    (h : Present s C l X) :
    (X = C ∧ ∀ st ∈ l.head?, s ≤ st.time) ∨
      ∃ (j : ℕ) (hj : j < l.length), l[j].time ≤ s ∧ (∀ st ∈ l[j + 1]?, s ≤ st.time) ∧
        X = l[j].cache := by
  induction l generalizing C with
  | nil => left; exact ⟨h, by simp⟩
  | cons st rest ih =>
    rcases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · left; exact ⟨rfl, by simpa using h1⟩
    · rcases ih st.cache h2 with ⟨rfl, h3⟩ | ⟨j, hj, h3, h4, rfl⟩
      · right
        refine ⟨0, by simp, h1, ?_, rfl⟩
        intro x hx
        apply h3
        cases rest with
        | nil => simp at hx
        | cons y ys => simpa using hx
      · right
        exact ⟨j + 1, by simp; omega, by simpa using h3, by simpa using h4, by simp⟩

theorem present_of_idx {s : ℝ} (C : Finset Page) (l : Schedule Page) (X : Finset Page)
    (hc : l.Pairwise fun a b => a.time ≤ b.time)
    (h : (X = C ∧ ∀ st ∈ l.head?, s ≤ st.time) ∨
      ∃ (j : ℕ) (hj : j < l.length), l[j].time ≤ s ∧ (∀ st ∈ l[j + 1]?, s ≤ st.time) ∧
        X = l[j].cache) :
    Present s C l X := by
  induction l generalizing C with
  | nil =>
    rcases h with ⟨rfl, -⟩ | ⟨j, hj, -⟩
    · rfl
    · simp at hj
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    rcases h with ⟨rfl, h1⟩ | ⟨j, hj, h1, h2, rfl⟩
    · exact Or.inl ⟨h1 st rfl, rfl⟩
    · cases j with
      | zero =>
        refine Or.inr ⟨by simpa using h1, ih st.cache hc.2 (Or.inl ⟨by simp, ?_⟩)⟩
        intro x hx
        apply h2
        cases rest with
        | nil => simp at hx
        | cons y ys => simpa using hx
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        refine Or.inr ⟨?_, ih st.cache hc.2
          (Or.inr ⟨j, hj', by simpa using h1, by simpa using h2, by simp⟩)⟩
        exact le_trans (hc.1 _ (List.getElem_mem hj')) (by simpa using h1)

theorem pairwise_of_const (t : ℝ) (l : Schedule Page) (h : ∀ x ∈ l, x.time = t) :
    l.Pairwise fun a b => a.time ≤ b.time := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih fun y hy => h y (by simp [hy])⟩
    rw [h x (by simp), h y (by simp [hy])]

theorem swap_card {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    (insert p (C.erase q)).card = C.card := by
  have hp' : p ∉ C.erase q := fun h => hp (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hp', Finset.card_erase_of_mem hq]
  have : 0 < C.card := Finset.card_pos.2 ⟨q, hq⟩
  omega

/-! ### Rounds -/

section Round

variable (t : ℝ) (Cnew : Finset Page)

theorem roundL_time (C : Finset Page) (ps : List Page) :
    ∀ x ∈ roundL t Cnew C ps, x.time = t := by
  induction ps generalizing C with
  | nil => simp [roundL]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact ih _ x hx
    · exact ih C

theorem roundL_card (C : Finset Page) (ps : List Page) :
    ∀ x ∈ roundL t Cnew C ps, x.cache.card = C.card := by
  induction ps generalizing C with
  | nil => simp [roundL]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · have hq := (Finset.mem_sdiff.1 h.2.choose_spec).1
      have hc := swap_card h.1 hq
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc
      · rw [ih _ x hx, hc]
    · exact ih C

theorem roundL_swap (C : Finset Page) (ps : List Page) :
    SwapFrom C (roundL t Cnew C ps) := by
  induction ps generalizing C with
  | nil => simp [roundL, SwapFrom]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · exact ⟨⟨p, _, h.1, (Finset.mem_sdiff.1 h.2.choose_spec).1, rfl⟩, ih _⟩
    · exact ih C

theorem roundL_last (C : Finset Page) (ps : List Page) (hk : Cnew.card ≤ C.card)
    (hsub : ∀ x ∈ Cnew, x ∈ C ∨ x ∈ ps) :
    Cnew ⊆ lastCache C (roundL t Cnew C ps) := by
  induction ps generalizing C with
  | nil =>
    intro x hx
    rcases hsub x hx with h | h
    · exact h
    · simp at h
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · have hq := Finset.mem_sdiff.1 h.2.choose_spec
      apply ih
      · rw [swap_card h.1 hq.1]; exact hk
      · intro x hx
        rcases hsub x hx with hxC | hxp
        · left
          apply Finset.mem_insert_of_mem
          refine Finset.mem_erase.2 ⟨?_, hxC⟩
          rintro rfl; exact hq.2 hx
        · rcases List.mem_cons.1 hxp with rfl | hxp
          · left; exact Finset.mem_insert_self _ _
          · right; exact hxp
    · apply ih C hk
      intro x hx
      rcases hsub x hx with hxC | hxp
      · left; exact hxC
      · rcases List.mem_cons.1 hxp with rfl | hxp
        · left
          by_cases hpC : x ∈ C
          · exact hpC
          · exfalso
            have hne : ¬ (C \ Cnew).Nonempty := fun hn => h ⟨hpC, hn⟩
            rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
            have := Finset.eq_of_subset_of_card_le hne hk
            exact hpC (this ▸ hx)
        · right; exact hxp

theorem roundL_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (Cold : Finset Page)
    (C : Finset Page) (ps : List Page) (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∈ Cnew)
    (hinv : Cold ∩ Cnew ⊆ C) :
    costFrom w C (roundL t Cnew C ps) ≤ ∑ p ∈ ps.toFinset \ Cold, w p := by
  induction ps generalizing C with
  | nil => simp [roundL, costFrom]
  | cons p ps ih =>
    rw [List.nodup_cons] at hnd
    have hpN : p ∈ Cnew := hps p (by simp)
    have hps' : ∀ x ∈ ps, x ∈ Cnew := fun x hx => hps x (by simp [hx])
    have hsub : ps.toFinset \ Cold ⊆ (p :: ps).toFinset \ Cold :=
      Finset.sdiff_subset_sdiff (by intro x; simp; tauto) (Finset.Subset.refl _)
    simp only [roundL]
    split_ifs with h
    · have hq := Finset.mem_sdiff.1 h.2.choose_spec
      simp only [costFrom]
      have hpCold : p ∉ Cold := fun hc => h.1 (hinv (Finset.mem_inter.2 ⟨hc, hpN⟩))
      have h1 : ∑ x ∈ insert p (C.erase h.2.choose) \ C, w x ≤ w p := by
        calc ∑ x ∈ insert p (C.erase h.2.choose) \ C, w x ≤ ∑ x ∈ {p}, w x := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                rw [Finset.mem_sdiff, Finset.mem_insert] at hx
                rcases hx with ⟨rfl | hx, hxC⟩
                · simp
                · exact absurd (Finset.mem_of_mem_erase hx) hxC
              · intro x _ _; exact hw x
          _ = w p := by simp
      have h2 := ih (insert p (C.erase h.2.choose)) hnd.2 hps' (by
        intro x hx
        apply Finset.mem_insert_of_mem
        refine Finset.mem_erase.2 ⟨?_, hinv hx⟩
        rintro rfl; exact hq.2 (Finset.mem_inter.1 hx).2)
      have h3 : (p :: ps).toFinset \ Cold = insert p (ps.toFinset \ Cold) := by
        rw [List.toFinset_cons, Finset.insert_sdiff_of_notMem _ hpCold]
      rw [h3, Finset.sum_insert (by simp [hnd.1])]
      linarith
    · exact le_trans (ih C hnd.2 hps' hinv)
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x))

end Round

theorem round_time (st : Step Page) (C : Finset Page) : ∀ x ∈ round st C, x.time = st.time :=
  roundL_time _ _ _ _

theorem round_card (st : Step Page) (C : Finset Page) :
    ∀ x ∈ round st C, x.cache.card = C.card :=
  roundL_card _ _ _ _

theorem round_last (st : Step Page) (C : Finset Page) (hk : st.cache.card ≤ C.card) :
    st.cache ⊆ lastCache C (round st C) := by
  apply roundL_last _ _ _ _ hk
  intro x hx
  by_cases hxC : x ∈ C
  · left; exact hxC
  · right; simp [hx, hxC]

theorem round_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (Cold C : Finset Page) (st : Step Page)
    (hsub : Cold ⊆ C) : costFrom w C (round st C) ≤ ∑ p ∈ st.cache \ Cold, w p := by
  refine le_trans (roundL_cost _ _ w hw Cold C _ (Finset.nodup_toList _) ?_ ?_) ?_
  · intro p hp; exact (Finset.mem_sdiff.1 (Finset.mem_toList.1 hp)).1
  · exact fun x hx => hsub (Finset.mem_inter.1 hx).1
  · rw [Finset.toList_toFinset]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _)
    · intro x _ _; exact hw x

/-! ### The whole construction -/

theorem build_time (C : Finset Page) (S : Schedule Page) :
    ∀ x ∈ build C S, ∃ y ∈ S, x.time = y.time := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ⟨st, by simp, round_time st C x hx⟩
    · obtain ⟨y, hy, e⟩ := ih _ x hx
      exact ⟨y, by simp [hy], e⟩

theorem build_chrono (C : Finset Page) (S : Schedule Page)
    (hc : S.Pairwise fun a b => a.time ≤ b.time) :
    (build C S).Pairwise fun a b => a.time ≤ b.time := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    simp only [build]
    rw [List.pairwise_append]
    refine ⟨pairwise_of_const st.time _ (round_time st C), ih _ hc.2, ?_⟩
    intro a ha b hb
    obtain ⟨y, hy, e⟩ := build_time _ rest b hb
    rw [round_time st C a ha, e]
    exact hc.1 y hy

theorem build_card (k : ℕ) (C : Finset Page) (S : Schedule Page) (hC : C.card = k)
    (hcap : ∀ st ∈ S, st.cache.card ≤ k) : ∀ x ∈ build C S, x.cache.card = k := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [round_card st C x hx, hC]
    · refine ih _ ?_ (fun y hy => hcap y (by simp [hy])) x hx
      exact lastCache_card k C _ hC (fun y hy => by rw [round_card st C y hy, hC])

theorem build_swap (C : Finset Page) (S : Schedule Page) : SwapFrom C (build C S) := by
  induction S generalizing C with
  | nil => simp [build, SwapFrom]
  | cons st rest ih =>
    simp only [build]
    rw [swapFrom_append]
    exact ⟨roundL_swap _ _ _ _, ih _⟩

theorem build_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (k : ℕ) (C C' : Finset Page)
    (S : Schedule Page) (hsub : C ⊆ C') (hC : C'.card = k)
    (hcap : ∀ st ∈ S, st.cache.card ≤ k) :
    costFrom w C' (build C' S) ≤ costFrom w C S := by
  induction S generalizing C C' with
  | nil => simp [build, costFrom]
  | cons st rest ih =>
    simp only [build, costFrom]
    rw [costFrom_append]
    have h1 := round_cost w hw C C' st hsub
    have h2 := ih st.cache (lastCache C' (round st C'))
      (round_last st C' (by rw [hC]; exact hcap st (by simp)))
      (lastCache_card k C' _ hC (fun y hy => by rw [round_card st C' y hy, hC]))
      (fun y hy => hcap y (by simp [hy]))
    linarith

theorem build_present {s : ℝ} (k : ℕ) (C C' : Finset Page) (S : Schedule Page)
    (hsub : C ⊆ C') (hC : C'.card = k) (hcap : ∀ st ∈ S, st.cache.card ≤ k)
    (hc : S.Pairwise fun a b => a.time ≤ b.time) (X : Finset Page) (hX : Present s C S X) :
    ∃ Y, X ⊆ Y ∧ Present s C' (build C' S) Y := by
  induction S generalizing C C' with
  | nil => exact ⟨C', by rw [show X = C from hX]; exact hsub, rfl⟩
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    simp only [build]
    rcases hX with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · refine ⟨C', hsub, present_self _ _ ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [round_time st C' x hx]; exact h1
      · obtain ⟨y, hy, e⟩ := build_time _ rest x hx
        rw [e]; exact le_trans h1 (hc.1 y hy)
    · obtain ⟨Y, hXY, hY⟩ := ih st.cache (lastCache C' (round st C'))
        (round_last st C' (by rw [hC]; exact hcap st (by simp)))
        (lastCache_card k C' _ hC (fun y hy => by rw [round_card st C' y hy, hC]))
        (fun y hy => hcap y (by simp [hy])) hc.2 h2
      refine ⟨Y, hXY, present_append _ _ _ _ ?_ hY⟩
      intro x hx; rw [round_time st C' x hx]; exact h1

open scoped PagingWithDelay.InstanceNotation in
/-- The swap normal form, stated with the recursive notion `SwapFrom`. -/
theorem exists_swapFrom {input : Instance Page} (hv : input.Valid) {σ : Request Page → ℝ}
    {S : Schedule Page} (hS : S.FeasibleBy input σ) :
    ∃ S' : Schedule Page, S'.FeasibleBy input σ ∧ SwapFrom input.initialCache S' ∧
      S'.fetchCost input ≤ S.fetchCost input := by
  refine ⟨build input.initialCache S, ⟨build_chrono _ _ hS.chronological, ?_, ?_⟩,
    build_swap _ _, ?_⟩
  · intro st hst
    rw [build_card k _ S hv.initialCache_card hS.capacity st hst]
  · intro ρ hρ
    obtain ⟨s, h1, h2, h3⟩ := hS.serves ρ hρ
    have key : ∃ X, ρ.page ∈ X ∧ Present s input.initialCache S X := by
      rcases h3 with ⟨hp, h⟩ | ⟨j, hj, ha, hb, hp⟩
      · exact ⟨_, hp, present_of_idx _ _ _ hS.chronological (Or.inl ⟨rfl, h⟩)⟩
      · exact ⟨_, hp, present_of_idx _ _ _ hS.chronological (Or.inr ⟨j, hj, ha, hb, rfl⟩)⟩
    obtain ⟨X, hpX, hX⟩ := key
    obtain ⟨Y, hXY, hY⟩ := build_present k _ _ S (subset_refl _)
      hv.initialCache_card hS.capacity hS.chronological X hX
    refine ⟨s, h1, h2, ?_⟩
    rcases idx_of_present _ _ _ hY with ⟨rfl, h⟩ | ⟨j, hj, ha, hb, rfl⟩
    · exact Or.inl ⟨hXY hpX, h⟩
    · exact Or.inr ⟨j, hj, ha, hb, hXY hpX⟩
  · exact build_cost w (fun p => (hv.weight_pos p).le) k _ _ S
      (subset_refl _) hv.initialCache_card hS.capacity

end NF

/-! ## Caches, evictions and the lazy optimum -/

/-- The cache before step `j` (for `j ≤ length`, the cache after the first `j` steps). -/
def cacheBeforeStep (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  match j with
  | 0 => input.initialCache
  | j + 1 => (S[j]?.map Step.cache).getD input.initialCache

/-- The cache after all steps with time `≤ t` (for a chronological schedule). -/
noncomputable def cacheAt (input : Instance Page) (S : Schedule Page) (t : ℝ) : Finset Page :=
  cacheBeforeStep input S (S.filter fun step => decide (step.time ≤ t)).length

/-- Swap normal form: chronological, and every step evicts exactly one cached page and fetches exactly one page not cached. -/
structure SwapForm (input : Instance Page) (S : Schedule Page) : Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  swap : ∀ (j : ℕ) (h : j < S.length), ∃ p q,
    p ∉ cacheBeforeStep input S j ∧ q ∈ cacheBeforeStep input S j ∧
      S[j].cache = insert p ((cacheBeforeStep input S j).erase q)

/-- The pages fetched at step `j`. -/
def fetchedAt (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  cacheBeforeStep input S (j + 1) \ cacheBeforeStep input S j

/-- The pages evicted at step `j`. -/
def evictedAt (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  cacheBeforeStep input S j \ cacheBeforeStep input S (j + 1)

/-- The distinct times of the steps. -/
noncomputable def stepTimes (S : Schedule Page) : Finset ℝ :=
  (S.map PagingWithDelay.Step.time).toFinset

/-! ### Helpers -/

/-- The cache before step `j`, from an arbitrary start cache `C`. -/
def cbs (C : Finset Page) (S : Schedule Page) : ℕ → Finset Page
  | 0 => C
  | j + 1 => (S[j]?.map Step.cache).getD C

theorem cacheBeforeStep_eq_cbs (S : Schedule Page) (j : ℕ) :
    cacheBeforeStep input S j = cbs input.initialCache S j := by
  cases j <;> rfl

theorem cbs_succ_of_lt (C : Finset Page) {S : Schedule Page} {j : ℕ} (h : j < S.length) :
    cbs C S (j + 1) = S[j].cache := by
  simp [cbs, List.getElem?_eq_getElem h]

theorem cbs_succ_of_le (C : Finset Page) {S : Schedule Page} {j : ℕ} (h : S.length ≤ j) :
    cbs C S (j + 1) = C := by
  simp [cbs, List.getElem?_eq_none h]

theorem cbs_cons (C : Finset Page) (st : Step Page) (rest : Schedule Page) {j : ℕ}
    (h : j ≤ rest.length) : cbs C (st :: rest) (j + 1) = cbs st.cache rest j := by
  cases j with
  | zero => simp [cbs]
  | succ j =>
    rw [cbs_succ_of_lt _ (by simp; omega), cbs_succ_of_lt _ (by omega)]
    simp

theorem cacheBeforeStep_succ_of_lt {S : Schedule Page} {j : ℕ} (h : j < S.length) :
    cacheBeforeStep input S (j + 1) = S[j].cache := by
  rw [cacheBeforeStep_eq_cbs, cbs_succ_of_lt _ h]

theorem cacheBeforeStep_succ_of_le {S : Schedule Page} {j : ℕ} (h : S.length ≤ j) :
    cacheBeforeStep input S (j + 1) = input.initialCache := by
  rw [cacheBeforeStep_eq_cbs, cbs_succ_of_le _ h]

theorem costFrom_eq_sum (w : Page → ℝ) (C : Finset Page) (S : Schedule Page) :
    costFrom w C S = ∑ j ∈ Finset.range S.length, ∑ p ∈ cbs C S (j + 1) \ cbs C S j, w p := by
  induction S generalizing C with
  | nil => simp [costFrom]
  | cons st rest ih =>
    rw [List.length_cons, Finset.sum_range_succ', costFrom, ih st.cache]
    have h0 : cbs C (st :: rest) (0 + 1) = st.cache := by simp [cbs]
    rw [h0, show cbs C (st :: rest) 0 = C from rfl, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [cbs_cons _ _ _ (by omega), cbs_cons _ _ _ (by omega)]

open scoped PagingWithDelay.InstanceNotation

theorem swapFrom_idx (C : Finset Page) (S : Schedule Page) (h : NF.SwapFrom C S) :
    ∀ (j : ℕ) (hj : j < S.length), ∃ p q, p ∉ cbs C S j ∧ q ∈ cbs C S j ∧
      S[j].cache = insert p ((cbs C S j).erase q) := by
  induction S generalizing C with
  | nil => intro j hj; simp at hj
  | cons st rest ih =>
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      rw [cbs_cons _ _ _ hj'.le]
      simpa using ih st.cache h.2 j hj'

/-- The number of steps with time `≤ t`. -/
noncomputable def numLE (S : Schedule Page) (t : ℝ) : ℕ :=
  (S.filter fun step => decide (step.time ≤ t)).length

theorem cacheAt_def (S : Schedule Page) (t : ℝ) :
    cacheAt input S t = cacheBeforeStep input S (numLE S t) := rfl

theorem numLE_le_length (S : Schedule Page) (t : ℝ) : numLE S t ≤ S.length :=
  List.length_filter_le _ _

theorem time_mono {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {i j : ℕ} (hij : i ≤ j) (hj : j < S.length) :
    S[i].time ≤ S[j].time := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.1 hc i j (by omega) hj hlt

theorem lt_numLE_iff {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} {i : ℕ} (hi : i < S.length) : i < numLE S t ↔ S[i].time ≤ t := by
  induction S generalizing i with
  | nil => simp at hi
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    unfold numLE
    rw [List.filter_cons]
    by_cases hst : st.time ≤ t
    · simp only [hst, decide_true, if_true, List.length_cons]
      cases i with
      | zero => simpa using hst
      | succ i =>
        have hi' : i < rest.length := by simpa using hi
        have := ih hc.2 hi'
        unfold numLE at this
        simp only [List.getElem_cons_succ]
        exact Nat.succ_lt_succ_iff.trans this
    · simp only [hst, decide_false, Bool.false_eq_true, if_false]
      have hnil : rest.filter (fun step => decide (step.time ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := hc.1 a ha
        simp only [decide_eq_true_eq]
        linarith [not_le.1 hst]
      rw [hnil]
      simp only [List.length_nil, Nat.not_lt_zero, false_iff, not_le]
      cases i with
      | zero => simpa using not_le.1 hst
      | succ i =>
        have hi' : i < rest.length := by simpa using hi
        simp only [List.getElem_cons_succ]
        exact lt_of_lt_of_le (not_le.1 hst) (hc.1 _ (List.getElem_mem hi'))

theorem head_le {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time) {s : ℝ}
    (h : ∀ st ∈ S.head?, s ≤ st.time) {i : ℕ} (hi : i < S.length) : s ≤ S[i].time := by
  cases S with
  | nil => simp at hi
  | cons x xs =>
    have h0 : s ≤ x.time := h x rfl
    exact le_trans h0 (time_mono hc (Nat.zero_le i) hi)

theorem cacheAt_eq_initial {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} (h : ∀ st ∈ S.head?, t < st.time) : cacheAt input S t = input.initialCache := by
  rw [cacheAt_def]
  have : numLE S t = 0 := by
    by_contra hne
    have hpos : 0 < numLE S t := Nat.pos_of_ne_zero hne
    have h0 : 0 < S.length := lt_of_lt_of_le hpos (numLE_le_length S t)
    have h1 := (lt_numLE_iff hc h0).1 hpos
    cases S with
    | nil => simp at h0
    | cons x xs => exact absurd h1 (not_le.2 (h x rfl))
  rw [this]; rfl

theorem cacheAt_eq_of_last {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} {j : ℕ} (hj : j < S.length) (h1 : S[j].time ≤ t)
    (h2 : ∀ st ∈ S[j + 1]?, t < st.time) : cacheAt input S t = S[j].cache := by
  rw [cacheAt_def]
  have hn : numLE S t = j + 1 := by
    have ha := (lt_numLE_iff hc hj).2 h1
    have hb : numLE S t ≤ j + 1 := by
      by_contra hne
      push_neg at hne
      have hl : j + 1 < S.length := lt_of_lt_of_le hne (numLE_le_length S t)
      have := (lt_numLE_iff hc hl).1 hne
      exact absurd this (not_le.2 (h2 _ (List.getElem?_eq_getElem hl)))
    omega
  rw [hn, cacheBeforeStep_succ_of_lt hj]

theorem exists_last_evict {S : Schedule Page} {p : Page} {a b : ℕ} (hab : a ≤ b)
    (hp : p ∈ cacheBeforeStep input S a) (hp' : p ∉ cacheBeforeStep input S b) :
    ∃ i, a ≤ i ∧ i < b ∧ p ∈ evictedAt input S i ∧
      ∀ i', i < i' → i' < b → p ∉ evictedAt input S i' := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hp hp'
  | succ b hab ih =>
    by_cases hb : p ∈ cacheBeforeStep input S b
    · exact ⟨b, hab, by omega, Finset.mem_sdiff.2 ⟨hb, hp'⟩, fun i' h1 h2 => by omega⟩
    · obtain ⟨i, h1, h2, h3, h4⟩ := ih hb
      refine ⟨i, h1, by omega, h3, fun i' hi1 hi2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
      · exact h4 i' hi1 hi2
      · exact fun hmem => hb (Finset.mem_sdiff.1 hmem).1

theorem swap_sdiff_left {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    C \ insert p (C.erase q) = {q} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hne
    exact hn (Or.inr ⟨hne, hx⟩)
  · rintro rfl
    refine ⟨hq, fun h => h.elim (fun e => hp (e ▸ hq)) (fun h => h.1 rfl)⟩

theorem swap_sdiff_right {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    insert p (C.erase q) \ C = {p} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | ⟨-, hx⟩, hn⟩
    · exact hx
    · exact absurd hx hn
  · rintro rfl
    exact ⟨Or.inl rfl, hp⟩

theorem SwapForm.step {S : Schedule Page} (hS : SwapForm input S) {j : ℕ} (hj : j < S.length) :
    ∃ p q, p ∉ cacheBeforeStep input S j ∧ q ∈ cacheBeforeStep input S j ∧
      cacheBeforeStep input S (j + 1) = insert p ((cacheBeforeStep input S j).erase q) ∧
      fetchedAt input S j = {p} ∧ evictedAt input S j = {q} := by
  obtain ⟨p, q, hp, hq, he⟩ := hS.swap j hj
  have he' : cacheBeforeStep input S (j + 1) = insert p ((cacheBeforeStep input S j).erase q) := by
    rw [cacheBeforeStep_succ_of_lt hj, he]
  refine ⟨p, q, hp, hq, he', ?_, ?_⟩
  · unfold fetchedAt; rw [he', swap_sdiff_right hp hq]
  · unfold evictedAt; rw [he', swap_sdiff_left hp hq]

/-- The lazy optimum of `sec:problem`, in the stronger swap form: a feasible schedule with service times `σ` can be replaced by a swap-form schedule that serves every request `ρ` by `σ ρ`, at no larger fetch cost. -/
theorem exists_swapForm (hv : input.Valid) {S : Schedule Page} (hF : S.Feasible input)
    (hσ : S.ServiceTimes input σ) :
    ∃ S' : Schedule Page, S'.FeasibleBy input σ ∧ SwapForm input S' ∧
      S'.fetchCost input ≤ S.fetchCost input := by
  obtain ⟨S', hF', hsw, hc⟩ := NF.exists_swapFrom hv (hF.feasibleBy hσ)
  refine ⟨S', hF', ⟨hF'.chronological, fun j hj => ?_⟩, hc⟩
  simp only [cacheBeforeStep_eq_cbs]
  exact swapFrom_idx _ _ hsw j hj

section SwapForm

variable (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
include hv hS

theorem card_cacheBeforeStep (j : ℕ) : (cacheBeforeStep input S j).card = k := by
  induction j with
  | zero => exact hv.initialCache_card
  | succ j ih =>
    by_cases hj : j < S.length
    · obtain ⟨p, q, hp, hq, he, -, -⟩ := hS.step hj
      rw [he, NF.swap_card hp hq, ih]
    · rw [cacheBeforeStep_succ_of_le (not_lt.1 hj)]; exact hv.initialCache_card

/-- In swap form, the cache always holds exactly `k` pages. -/
theorem card_cacheAt (t : ℝ) : (cacheAt input S t).card = k := by
  exact card_cacheBeforeStep hv hS _

/-- The fetch cost is the total weight of the pages fetched at the steps. -/
theorem fetchCost_eq_sum_fetched :
    S.fetchCost input = ∑ j ∈ Finset.range S.length, ∑ p ∈ fetchedAt input S j, w p := by
  unfold fetchCost fetchedAt
  simp only [cacheBeforeStep_eq_cbs]
  exact costFrom_eq_sum _ _ _

/-- `obs:evictions`: the total weight of evictions is at most the fetch cost plus `w(C₀)`. -/
theorem sum_evicted_le :
    ∑ j ∈ Finset.range S.length, ∑ p ∈ evictedAt input S j, w p ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p := by
  have hw : ∀ p, 0 ≤ w p := fun p => (hv.weight_pos p).le
  rw [fetchCost_eq_sum_fetched hv hS]
  have key : ∀ j, ∑ p ∈ evictedAt input S j, w p =
      ∑ p ∈ fetchedAt input S j, w p +
        (∑ p ∈ cacheBeforeStep input S j, w p -
          ∑ p ∈ cacheBeforeStep input S (j + 1), w p) := by
    intro j
    unfold evictedAt fetchedAt
    have := Finset.sum_sdiff_sub_sum_sdiff (s₁ := cacheBeforeStep input S (j + 1))
      (s₂ := cacheBeforeStep input S j) (f := w)
    linarith
  simp only [key, Finset.sum_add_distrib]
  have htel := Finset.sum_range_sub'
    (fun j => ∑ p ∈ cacheBeforeStep input S j, w p) S.length
  beta_reduce at htel
  have h0 : cacheBeforeStep input S 0 = input.initialCache := rfl
  rw [h0] at htel
  have : 0 ≤ ∑ p ∈ cacheBeforeStep input S S.length, w p :=
    Finset.sum_nonneg (fun p _ => hw p)
  linarith

/-- Between two times, a function of the cache changes by at most the sum of its changes at the steps in between. -/
theorem cacheAt_change (F : Finset Page → ℝ) (α β : ℝ)
    (hF : ∀ C p q, p ∉ C → q ∈ C →
      F (insert p (C.erase q)) - F C ≤ α * w q + β * w p)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    F (cacheAt input S t₂) - F (cacheAt input S t₁) ≤
      ∑ j ∈ (Finset.range S.length).filter
          (fun j => ∃ h : j < S.length, t₁ < S[j].time ∧ S[j].time ≤ t₂),
        (α * ∑ q ∈ evictedAt input S j, w q +
          β * ∑ p ∈ fetchedAt input S j, w p) := by
  have hc := hS.chronological
  have hlen := numLE_le_length S t₂
  have h12 : numLE S t₁ ≤ numLE S t₂ := by
    by_contra h
    push_neg at h
    have hl : numLE S t₂ < S.length := lt_of_lt_of_le h (numLE_le_length S t₁)
    have := (lt_numLE_iff hc hl).1 h
    exact absurd ((lt_numLE_iff hc hl).2 (le_trans this ht)) (lt_irrefl _)
  have hset : (Finset.range S.length).filter
      (fun j => ∃ h : j < S.length, t₁ < S[j].time ∧ S[j].time ≤ t₂) =
      Finset.Ico (numLE S t₁) (numLE S t₂) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hj, hj', h1, h2⟩
      exact ⟨not_lt.1 (fun h => absurd ((lt_numLE_iff hc hj).1 h) (not_le.2 h1)),
        (lt_numLE_iff hc hj).2 h2⟩
    · rintro ⟨h1, h2⟩
      have hj : j < S.length := by omega
      exact ⟨hj, hj, not_le.1 (fun h => absurd ((lt_numLE_iff hc hj).2 h) (by omega)),
        (lt_numLE_iff hc hj).1 h2⟩
  have htel := Finset.sum_Ico_sub (fun j => F (cacheBeforeStep input S j)) h12
  beta_reduce at htel
  rw [hset, cacheAt_def, cacheAt_def, ← htel]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨p, q, hp, hq, he, hfe, hev⟩ := hS.step (show j < S.length by omega)
  rw [hfe, hev, he, Finset.sum_singleton, Finset.sum_singleton]
  exact hF _ p q hp hq

/-- Before the first step, the cache is the initial cache. -/
theorem cacheAt_of_lt {t : ℝ} (ht : ∀ step ∈ S, t < step.time) :
    cacheAt input S t = input.initialCache := by
  rw [cacheAt_def]
  have : numLE S t = 0 := by
    unfold numLE
    have hnil : S.filter (fun step => decide (step.time ≤ t)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simpa using ht a ha
    rw [hnil]; rfl
  rw [this]; rfl

/-- If no step happens in `(t₁, t₂]`, the cache is the same at `t₁` and `t₂`. -/
theorem cacheAt_eq_of_quiet {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hq : ∀ step ∈ S, ¬ (t₁ < step.time ∧ step.time ≤ t₂)) :
    cacheAt input S t₁ = cacheAt input S t₂ := by
  have hfil : S.filter (fun step => decide (step.time ≤ t₁)) =
      S.filter (fun step => decide (step.time ≤ t₂)) := by
    apply List.filter_congr
    intro x hx
    simp only [decide_eq_decide]
    constructor
    · intro h; linarith
    · intro h; by_contra h'; exact hq x hx ⟨not_le.1 h', h⟩
  unfold cacheAt
  rw [hfil]

end SwapForm


/-! ## Quiet windows, last evictions and lightest weights -/

section

variable (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
  (hF : S.FeasibleBy input σ)
include hv hS hF

/-- A quiet window. If the page of `ρ` is not cached at `t ≤ σ ρ` and no step happens in `(t, σ ρ]`, then `S` has served `ρ` by `t`; in particular `a_ρ ≤ t`. -/
theorem servedBy_of_quiet {ρ : Request Page} (hρ : ρ ∈ input.requests) {t : ℝ}
    (ht : t ≤ σ ρ) (hq : ∀ step ∈ S, ¬ (t < step.time ∧ step.time ≤ σ ρ))
    (hp : ρ.page ∉ cacheAt input S t) : ServedBy input σ S ρ t := by
  have hc := hS.chronological
  obtain ⟨s, h1, h2, h3⟩ := hF.serves ρ hρ
  by_cases hst : s ≤ t
  · exact ⟨s, h1, h2, hst, h3⟩
  · exfalso
    have hst' : t < s := not_le.1 hst
    apply hp
    rcases h3 with ⟨hpC, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
    · rw [cacheAt_eq_initial hc (fun st hst => lt_of_lt_of_le hst' (hh st hst))]
      exact hpC
    · have hjt : S[j].time ≤ t := by
        by_contra hcon
        exact hq _ (List.getElem_mem hj) ⟨not_le.1 hcon, le_trans ha h2⟩
      rw [cacheAt_eq_of_last hc hj hjt (fun st hst => lt_of_lt_of_le hst' (hb st hst))]
      exact hpj

/-- The last eviction of `p` at a step with time `≤ t`. -/
def IsLastEviction (input : Instance Page) (S : Schedule Page) (p : Page) (t : ℝ) (j : ℕ) :
    Prop :=
  ∃ h : j < S.length, S[j].time ≤ t ∧ p ∈ evictedAt input S j ∧
    ∀ j' (h' : j' < S.length), j < j' → S[j'].time ≤ t → p ∉ evictedAt input S j'

/-- Charging to the last eviction (`lem:chargeable`). If `S` has served a request `π` on `p` by `t` but `p` is not cached at `t`, then `S` has evicted `p` at a step with time `≤ t`, and the last such eviction is at a time `≥ a_π`. -/
theorem exists_lastEviction {π : Request Page} {t : ℝ} (hπ : ServedBy input σ S π t)
    (hp : π.page ∉ cacheAt input S t) :
    ∃ j, IsLastEviction input S π.page t j ∧
      ∃ h : j < S.length, π.arrival ≤ S[j].time := by
  have hc := hS.chronological
  obtain ⟨s, h1, h2, h3, h4⟩ := hπ
  have hn := numLE_le_length S t
  rw [cacheAt_def] at hp
  rcases h4 with ⟨hpC, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
  · obtain ⟨i, -, hi2, hi3, hi4⟩ :=
      exists_last_evict (input := input) (S := S) (a := 0) (Nat.zero_le _) hpC hp
    have hilen : i < S.length := by omega
    refine ⟨i, ⟨hilen, (lt_numLE_iff hc hilen).1 hi2, hi3, ?_⟩, hilen, ?_⟩
    · intro j' hj' hij ht'
      exact hi4 j' hij ((lt_numLE_iff hc hj').2 ht')
    · exact le_trans h1 (head_le hc hh hilen)
  · have hjn : j < numLE S t := (lt_numLE_iff hc hj).2 (le_trans ha h3)
    have hmem : π.page ∈ cacheBeforeStep input S (j + 1) := by
      rw [cacheBeforeStep_succ_of_lt hj]; exact hpj
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_last_evict (by omega) hmem hp
    have hilen : i < S.length := by omega
    refine ⟨i, ⟨hilen, (lt_numLE_iff hc hilen).1 hi2, hi3, ?_⟩, hilen, ?_⟩
    · intro j' hj' hij ht'
      exact hi4 j' hij ((lt_numLE_iff hc hj').2 ht')
    · have hj1 : j + 1 < S.length := by omega
      have := hb _ (List.getElem?_eq_getElem hj1)
      exact le_trans h1 (le_trans this (time_mono hc hi1 hilen))

/-- `lem:lightest` (lightest weights). If `m τ` is at most the weight of every page cached at the step time `τ`, then `∑_τ m τ` is at most the fetch cost of `S`. -/
theorem sum_stepTimes_le (m : ℝ → ℝ)
    (hm : ∀ τ ∈ stepTimes S, ∀ q ∈ cacheAt input S τ, m τ ≤ w q) :
    ∑ τ ∈ stepTimes S, m τ ≤ S.fetchCost input := by
  have hc := hS.chronological
  have hw : ∀ p, 0 ≤ w p := fun p => (hv.weight_pos p).le
  set g : ℝ → ℕ := fun τ => numLE S τ - 1 with hg
  have hA : ∀ τ ∈ stepTimes S, ∃ h : g τ < S.length, S[g τ].time = τ ∧ g τ + 1 = numLE S τ := by
    intro τ hτ
    unfold stepTimes at hτ
    rw [List.mem_toFinset, List.mem_map] at hτ
    obtain ⟨st, hst, rfl⟩ := hτ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hst
    have hin := (lt_numLE_iff hc hi (t := S[i].time)).2 le_rfl
    have hn := numLE_le_length S S[i].time
    have hgl : g S[i].time < S.length := by simp only [hg]; omega
    refine ⟨hgl, ?_, by simp only [hg]; omega⟩
    apply le_antisymm
    · exact (lt_numLE_iff hc hgl).1 (by simp only [hg]; omega)
    · exact time_mono hc (by simp only [hg]; omega) hgl
  have hinj : Set.InjOn g (stepTimes S : Set ℝ) := by
    intro τ hτ τ' hτ' heq
    obtain ⟨h1, e1, -⟩ := hA τ hτ
    obtain ⟨h2, e2, -⟩ := hA τ' hτ'
    rw [← e1, ← e2]
    simp only [heq]
  have hB : ∀ τ ∈ stepTimes S, m τ ≤ ∑ p ∈ fetchedAt input S (g τ), w p := by
    intro τ hτ
    obtain ⟨h1, e1, e2⟩ := hA τ hτ
    obtain ⟨p, q, hp, hq, he, hfe, hev⟩ := hS.step h1
    rw [hfe, Finset.sum_singleton]
    apply hm τ hτ
    rw [cacheAt_def, ← e2, he]
    exact Finset.mem_insert_self _ _
  rw [fetchCost_eq_sum_fetched hv hS]
  calc ∑ τ ∈ stepTimes S, m τ
      ≤ ∑ τ ∈ stepTimes S, ∑ p ∈ fetchedAt input S (g τ), w p :=
        Finset.sum_le_sum hB
    _ = ∑ j ∈ (stepTimes S).image g, ∑ p ∈ fetchedAt input S j, w p :=
        (Finset.sum_image (f := fun j => ∑ p ∈ fetchedAt input S j, w p) hinj).symm
    _ ≤ ∑ j ∈ Finset.range S.length, ∑ p ∈ fetchedAt input S j, w p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hj
          obtain ⟨h1, -, -⟩ := hA τ hτ
          exact Finset.mem_range.2 h1
        · intro j _ _
          exact Finset.sum_nonneg (fun p _ => hw p)

end


/-! ## Periods

A time `t` lies in the period of the step time `τ` if `τ` is the last step time `≤ t`. Every time after the first step lies in exactly one period, and the comparator's cache is constant on a period. -/

/-- `t` lies in the period starting at the step time `τ`. -/
def InPer (S : Schedule Page) (τ t : ℝ) : Prop :=
  τ ∈ stepTimes S ∧ τ ≤ t ∧ ∀ step ∈ S, ¬ (τ < step.time ∧ step.time ≤ t)

theorem mem_stepTimes {S : Schedule Page} {τ : ℝ} :
    τ ∈ stepTimes S ↔ ∃ step ∈ S, step.time = τ := by
  unfold stepTimes
  simp

theorem InPer.unique {S : Schedule Page} {τ τ' t : ℝ} (h : InPer S τ t) (h' : InPer S τ' t) :
    τ = τ' := by
  obtain ⟨hτ, hτt, hq⟩ := h
  obtain ⟨hτ', hτ't, hq'⟩ := h'
  obtain ⟨s, hs, rfl⟩ := mem_stepTimes.1 hτ
  obtain ⟨s', hs', rfl⟩ := mem_stepTimes.1 hτ'
  rcases lt_trichotomy s.time s'.time with hlt | heq | hgt
  · exact absurd ⟨hlt, hτ't⟩ (hq s' hs')
  · exact heq
  · exact absurd ⟨hgt, hτt⟩ (hq' s hs)

theorem InPer.exists_of_step {S : Schedule Page} {t : ℝ} (h : ∃ step ∈ S, step.time ≤ t) :
    ∃ τ, InPer S τ t := by
  have hne : ((stepTimes S).filter (· ≤ t)).Nonempty := by
    obtain ⟨s, hs, hst⟩ := h
    exact ⟨s.time, Finset.mem_filter.2 ⟨mem_stepTimes.2 ⟨s, hs, rfl⟩, hst⟩⟩
  have hm := Finset.max'_mem _ hne
  rw [Finset.mem_filter] at hm
  refine ⟨_, hm.1, hm.2, fun s hs ⟨h1, h2⟩ => ?_⟩
  have : s.time ∈ (stepTimes S).filter (· ≤ t) :=
    Finset.mem_filter.2 ⟨mem_stepTimes.2 ⟨s, hs, rfl⟩, h2⟩
  exact absurd (Finset.le_max' _ _ this) (not_le.2 h1)

theorem InPer.of_le {S : Schedule Page} {τ t₁ t₂ : ℝ} (h : InPer S τ t₂) (h₁ : τ ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) : InPer S τ t₁ :=
  ⟨h.1, h₁, fun s hs ⟨a, b⟩ => h.2.2 s hs ⟨a, b.trans h₁₂⟩⟩

theorem InPer.cacheAt_eq (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
    {τ t : ℝ} (h : InPer S τ t) : cacheAt input S t = cacheAt input S τ :=
  (cacheAt_eq_of_quiet hv hS h.2.1 h.2.2).symm


/-! ## Delay costs of groups of requests -/

/-- The delay cost `d_ρ(σ ρ - a_ρ)` of request `ρ`. -/
noncomputable def delayOf (σ : Request Page → ℝ) (ρ : Request Page) : ℝ :=
  ρ.delay (σ ρ - ρ.arrival)

/-- The delay cost of the requests with index in `I`. -/
noncomputable def delayCostOn (input : Instance Page) (σ : Request Page → ℝ)
    (I : Finset (Fin input.requests.length)) : ℝ :=
  ∑ i ∈ I, delayOf σ input.requests[i]

/-- The total delay cost `∑_ρ d_ρ(σ ρ - a_ρ)`. -/
noncomputable def totalDelay (input : Instance Page) (σ : Request Page → ℝ) : ℝ :=
  (input.requests.map fun ρ => ρ.delay (σ ρ - ρ.arrival)).sum

theorem costWith_eq (S : Schedule Page) :
    S.costWith input σ = S.fetchCost input + totalDelay input σ := rfl

theorem totalDelay_eq_delayCostOn_univ :
    totalDelay input σ = delayCostOn input σ Finset.univ := by
  unfold totalDelay delayCostOn delayOf
  exact (Fin.sum_univ_fun_getElem input.requests (fun ρ => ρ.delay (σ ρ - ρ.arrival))).symm

theorem delayOf_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    {ρ : Request Page} (hρ : ρ ∈ input.requests) : 0 ≤ delayOf σ ρ := by
  unfold delayOf
  rw [← hv.delay_zero ρ hρ]
  exact hv.delay_mono ρ hρ (by linarith [hσ ρ hρ])

theorem delayOf_getElem_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (i : Fin input.requests.length) : 0 ≤ delayOf σ input.requests[i] :=
  delayOf_nonneg hv hσ (List.getElem_mem _)

theorem delayCostOn_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (I : Finset (Fin input.requests.length)) : 0 ≤ delayCostOn input σ I :=
  Finset.sum_nonneg fun i _ => delayOf_getElem_nonneg hv hσ i

theorem totalDelay_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) :
    0 ≤ totalDelay input σ := by
  rw [totalDelay_eq_delayCostOn_univ]; exact delayCostOn_nonneg hv hσ _

theorem delayCostOn_mono (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    {I J : Finset (Fin input.requests.length)} (h : I ⊆ J) :
    delayCostOn input σ I ≤ delayCostOn input σ J :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => delayOf_getElem_nonneg hv hσ i

theorem delayCostOn_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) (I : Finset (Fin input.requests.length)) :
    delayCostOn input σ I ≤ totalDelay input σ := by
  rw [totalDelay_eq_delayCostOn_univ]
  exact delayCostOn_mono hv hσ (Finset.subset_univ I)

/-- The delay costs of pairwise disjoint groups of requests (as index sets) sum to at most the total delay cost. -/
theorem sum_delayCostOn_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {ι : Type*} (G : Finset ι)
    (I : ι → Finset (Fin input.requests.length)) (hdisj : (G : Set ι).PairwiseDisjoint I) :
    ∑ g ∈ G, delayCostOn input σ (I g) ≤ totalDelay input σ := by
  classical
  unfold delayCostOn
  rw [← Finset.sum_biUnion hdisj]
  exact delayCostOn_le_totalDelay hv hσ _

/-- The form used by the charging arguments: if pairwise disjoint groups `g` of requests have delay cost at least `X g`, then `∑_g X g ≤ ∑_ρ d_ρ(σ ρ - a_ρ)`. -/
theorem sum_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {ι : Type*} (G : Finset ι)
    (I : ι → Finset (Fin input.requests.length)) (hdisj : (G : Set ι).PairwiseDisjoint I)
    (X : ι → ℝ) (hX : ∀ g ∈ G, X g ≤ delayCostOn input σ (I g)) :
    ∑ g ∈ G, X g ≤ totalDelay input σ :=
  (Finset.sum_le_sum hX).trans (sum_delayCostOn_le_totalDelay hv hσ G I hdisj)

/-! ## Delay lower bounds from not being served -/

section Served

variable {S : Schedule Page} (hF : S.FeasibleBy input σ)
include hF

/-- If `S` (serving every request `ρ` by `σ ρ`) has not served `ρ` by `t`, then `t < σ ρ`. -/
theorem lt_of_not_servedBy {ρ : Request Page} (hρ : ρ ∈ input.requests) {t : ℝ}
    (hn : ¬ ServedBy input σ S ρ t) : t < σ ρ := by
  by_contra hle
  push_neg at hle
  obtain ⟨s, h1, h2, h3⟩ := hF.serves ρ hρ
  exact hn ⟨s, h1, h2, le_trans h2 hle, h3⟩

/-- If `S` has not served `ρ` by `t`, the delay cost of `ρ` is at least `d_ρ(t - a_ρ)`. -/
theorem delay_le_of_not_servedBy (hv : input.Valid) {ρ : Request Page}
    (hρ : ρ ∈ input.requests) {t : ℝ}
    (hn : ¬ ServedBy input σ S ρ t) :
    ρ.delay (t - ρ.arrival) ≤ delayOf σ ρ :=
  hv.delay_mono ρ hρ (by linarith [lt_of_not_servedBy hF hρ hn])

/-- Index form of `delay_le_of_not_servedBy`. -/
theorem delay_le_of_not_servedBy' (hv : input.Valid) (i : Fin input.requests.length) {t : ℝ}
    (hn : ¬ ServedBy input σ S input.requests[i] t) :
    input.requests[i].delay (t - input.requests[i].arrival) ≤ delayOf σ input.requests[i] :=
  delay_le_of_not_servedBy hF hv (List.getElem_mem _) hn

end Served

end Schedule

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.Defs` -/
section

/-!
# Shared definitions of the analysis

Per-entry accounting of the run (fetches, evictions, lengths and budget payments of the moves), and the notions of the charging arguments against a comparator `S` with service times `σ`: chargeable visits (`def:chargeable`), the excess of a miss service, and overdue services.

The comparator is a schedule `S` serving each request `ρ` in `[a_ρ, σ ρ]` (`S.FeasibleBy input σ`), typically in swap form, with cache `cacheAt input S t` at time `t`; it has served `ρ` by `t` if `ServedBy input σ S ρ t`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch criticalEV hole holePayment tripCost)
open PagingWithDelay.Schedule (cacheAt ServedBy)

open Classical

noncomputable section

variable (input : Instance Page)

/-! ### Accounting of the run -/

/-- The fetch `w_p (x_p - δ)` of entry `i` if it is a critical service on `p`, else `0`. -/
def fetchAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => criticalFetch input (snapAt input i).x p
    | _ => 0
  else 0

/-- The weighted eviction `EV(λ)` of entry `i` if it is a critical service, else `0`. -/
def evAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => criticalEV input (snapAt input i).x p
    | _ => 0
  else 0

/-- The length `|λ|` of entry `i` if it is a critical service, else `0`. -/
def lenAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => serviceEnd input (snapAt input i).x p
    | _ => 0
  else 0

/-- The payment `W (1 - δ)` of entry `i` from the budget if it opens a hole, else `0`. -/
def holeAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .openHole e => holePayment input e
    | _ => 0
  else 0

/-- The cost `w_q (x_q - δ)` of entry `i` if it is a round trip on `q`, else `0` (paid from the budget). -/
def tripAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .trip _ π => tripCost input (snapAt input i).x π.page
    | _ => 0
  else 0

/-- `∑_λ fetch(λ)`. -/
def fetchTotal : ℝ := ∑ i ∈ Finset.range (log input).length, fetchAt input i

/-- `∑_λ EV(λ)`. -/
def evTotal : ℝ := ∑ i ∈ Finset.range (log input).length, evAt input i

/-- `∑_λ |λ|`. -/
def lenTotal : ℝ := ∑ i ∈ Finset.range (log input).length, lenAt input i

/-- The total payment for holes. -/
def holeTotal : ℝ := ∑ i ∈ Finset.range (log input).length, holeAt input i

/-- The total cost of round trips. -/
def tripTotal : ℝ := ∑ i ∈ Finset.range (log input).length, tripAt input i

/-! ### Visits -/

/-- The page visited at entry `i`: the page of a critical service or of a round trip. -/
def visitPage (i : ℕ) : Option Page :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => some p
    | .trip _ π => some π.page
    | _ => none
  else none

/-! ### The comparator -/

variable (σ : Request Page → ℝ) (S : Schedule Page)

/-- The comparator's delay cost `∑ d_ρ(σ ρ - a_ρ)` of the requests (by index) pending on page `p` in the loop state `s`. -/
def optDelayOn (s : Snap Page) (p : Page) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin input.requests.length =>
      input.requests[j] ∈ s.pending ∧ input.requests[j].page = p),
    Schedule.delayOf σ input.requests[j]

/-- `def:chargeable` (with "at least `w_p`" in (ii)): entry `i` is a visit of `p` (critical service or round trip) such that, right before it, (i) `p` is not in the comparator's cache and the comparator has served some pending request on `p`, or (ii) the comparator's delay cost for the pending requests on `p` is at least `w_p`. -/
def IsChargeable (i : ℕ) : Prop :=
  ∃ p, visitPage input i = some p ∧
    ((p ∉ cacheAt input S (entryTime input i) ∧
        ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
          ServedBy input σ S ρ (entryTime input i)) ∨
      w p ≤ optDelayOn input σ (snapAt input i) p)

/-- The weight of the page visited at entry `i` if it is chargeable, else `0`. -/
def chargeW (i : ℕ) : ℝ :=
  if IsChargeable input σ S i then
    match visitPage input i with
    | some p => w p
    | none => 0
  else 0

/-- `chargeW i` if entry `i` is a round trip, else `0`: the chargeable weight of round trips. -/
def tripChargeW (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .trip _ _ => chargeW input σ S i
    | _ => 0
  else 0

/-- `w_p` if entry `i` is a miss service on `p`, else `0`. -/
def missW (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => if p ∈ cacheAt input S (entryTime input i) then 0
        else w p
    | _ => 0
  else 0

/-- The levels `e` with `w_p ≤ 2^e ≤ w_max` whose weight is below every weight in the comparator's cache at time `t`. -/
def excessLevels (p : Page) (t : ℝ) : Finset ℤ :=
  (Finset.Icc (level input p) (maxLevel input)).filter
    (fun e => ∀ q ∈ cacheAt input S t, levelWeight e < w q)

/-- The excess `Exc(λ)` of entry `i`: if it is a miss service `λ` on `p`, the sum of `|λ|_W` over the levels `W` with `w_p ≤ W < w_min(OPT)`; else `0`. -/
def excessAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p =>
        if p ∈ cacheAt input S (entryTime input i) then 0
        else ∑ e ∈ excessLevels input S p (entryTime input i),
          levelLen input (snapAt input i).x p e
    | _ => 0
  else 0

/-- The delay at time `t` of the requests pending on `q` in the state `s` that the comparator has already served by `t`. -/
def servedDelay (s : Snap Page) (q : Page) (t : ℝ) : ℝ :=
  ((s.pending.filter fun ρ => decide (ρ.page = q ∧
      ServedBy input σ S ρ t)).map
    fun ρ => ρ.delay (t - ρ.arrival)).sum

/-- Page `q` is *overdue* in the state `s` at time `t`: the pending requests on `q` that the comparator has served have delay more than `w_q`. -/
def PageOverdue (s : Snap Page) (q : Page) (t : ℝ) : Prop :=
  w q < servedDelay input σ S s q t

/-- Entry `i` is an *overdue* critical service: on a page `p` such that some `q` with `w_q ≤ w_p` is overdue right before it. (The paper restricts this to miss services on pages below `w_min(OPT)`; only those have positive excess.) -/
def IsOverdue (i : ℕ) : Prop :=
  ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧
    ∃ q, w q ≤ w p ∧
      PageOverdue input σ S (snapAt input i) q (entryTime input i)

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.Telescope` -/
section

/-!
# Telescoping the Bregman potential (`prop:phaseD`, `lem:optmoves`, `prop:tele`)

* `critical_miss_len` (`prop:phaseD`, miss service, with lengths): the growth of `D(O ‖ x)` in a critical service on `r ∉ O` is at most `2 L w_r` plus `∑ |λ|_W` over the levels `w_r ≤ W < w_min(O)`. The rate of the pages `i ≠ r` is at most `1`, and at most `0` once some page of `O` is evicted (path time `≥ L w_q`).
* `fetchTotal_le` (`prop:tele`): the potential before entry `i` is `D(O ‖ x)` with `O` the comparator's cache at that time and `x` the state outside the current preemptive service (`baseState`). Only critical services change `x`; the comparator's steps in `(entryTime i, entryTime (i+1)]` change `O`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace TeleProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch IsRest IsFrac divergence bregG bregG_nonneg restPart restDeriv
  continuous_restPart hasDerivWithinAt_restPart restDeriv_eq divergence_start divergence_end
  sub_le_mul_of_deriv_right_le delta_lt_mdPath serviceEnd_nonneg serviceEnd_le
  levelWeight_level levelWeight_pos levelWeight_succ le_maxLevel delta_mul_exp_L log_delta
  NotEvicted criticalFetch_lt_weight divergence_change_cache divergence_le divergence_nonneg
  critical_hit)
open PagingWithDelay.Schedule (cacheAt evictedAt fetchedAt SwapForm cacheAt_change)

open Finset

/-! ### `prop:phaseD` for a miss service, with lengths -/

section Phase

open scoped InstanceNotation

variable {input : Instance Page} (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
  {x : Page → ℝ} (hx : IsRest input x) {r : Page} (hr : δ < x r)
  {O : Finset Page} (hO : O.card = k)
include hv h2 hx hr hO

/-- `prop:phaseD`, miss service, with the excess measured by lengths: the growth of `D` is at most `2 L w_r` plus `∑ |λ|_W` over the levels `W` with `w_r ≤ W ≤ w_max` below every weight of `O`. -/
theorem critical_miss_len (hrO : r ∉ O) :
    divergence input O (criticalState input x r) - divergence input O x ≤
      2 * L * w r +
        ∑ e ∈ (Finset.Icc (level input r) (maxLevel input)).filter
            (fun e => ∀ q ∈ O, levelWeight e < w q),
          levelLen input x r e := by
  have hbv := hv
  have hr' : δ < x r := hr
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_lt_of_le (Instance.delta_pos hv) (hx.1 i).1
  have hS0 := serviceEnd_nonneg hbv hx hr'
  have hL : 0 < L := Instance.L_pos hv
  have hd := Instance.delta_pos hv
  have hD0 := divergence_start hx O r
  have hD1 := divergence_end hbv hx hr' O
  set S := serviceEnd input x r with hS
  set A := restPart input O x r with hAdef
  have hAc : Continuous A := continuous_restPart hx0 O r
  have hAd := hasDerivWithinAt_restPart hbv hx0 O r
  set P : ℤ → ℝ := fun e => min (L * levelWeight e) S with hP
  have hP0 : ∀ e, 0 ≤ P e := fun e =>
    le_min (mul_nonneg hL.le (levelWeight_pos e).le) hS0
  have hPS : ∀ e, P e ≤ S := fun e => min_le_right _ _
  have hPmono : ∀ e, P e ≤ P (e + 1) := fun e =>
    min_le_min_right _ (mul_le_mul_of_nonneg_left
      (by rw [levelWeight_succ]; linarith [levelWeight_pos e]) hL.le)
  have hsum_nonneg : ∀ u, 0 ≤ ∑ i ∈ Finset.univ.erase r,
      (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := fun u =>
    Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hle1 : ∀ u, 0 ≤ u → u < S → restDeriv input O x r u ≤ 1 := by
    intro u hu0 huS
    have hxr := delta_lt_mdPath hbv hx hr' hu0 huS
    rw [restDeriv_eq hO, if_neg hrO]
    have : (0 : ℝ) < δ := hd
    linarith [hsum_nonneg u]
  have hle0 : ∀ u, 0 ≤ u → u < S → ∀ q ∈ O, L * w q ≤ u →
      restDeriv input O x r u ≤ 0 := by
    intro u hu0 huS q hq hqu
    have hxr := delta_lt_mdPath hbv hx hr' hu0 huS
    have hqr : q ≠ r := fun h => hrO (h ▸ hq)
    have hwq := hv.weight_pos q
    have hev : ¬ NotEvicted input x q u := by
      unfold NotEvicted
      push_neg
      have h1 : L ≤ u / w q := by rw [le_div_iff₀ hwq]; linarith
      have h2 : Real.exp L ≤ Real.exp (u / w q) := Real.exp_le_exp.mpr h1
      have h3 := delta_mul_exp_L hbv
      have h4 : δ * Real.exp L ≤ x q * Real.exp (u / w q) :=
        mul_le_mul (hx.1 q).1 h2 (Real.exp_pos _).le (hx0 q).le
      simpa using (show 1 ≤ x q * Real.exp (u / w q) by linarith)
    have hone : (1 : ℝ) ≤ ∑ i ∈ Finset.univ.erase r,
        (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
      have := Finset.single_le_sum
        (f := fun i => if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0)
        (fun i _ => by (try dsimp only); split_ifs <;> norm_num)
        (Finset.mem_erase.mpr ⟨hqr, Finset.mem_univ q⟩)
      try dsimp only at this
      rw [if_pos ⟨hev, hq⟩] at this
      exact this
    rw [restDeriv_eq hO, if_neg hrO]
    have : (0 : ℝ) < δ := hd
    linarith
  -- the initial segment `[0, L w_r)`
  have hwr : w r = levelWeight (level input r) :=
    (levelWeight_level hbv h2 r).symm
  have hinit : A (P (level input r)) - A 0 ≤ L * w r := by
    have := sub_le_mul_of_deriv_right_le (c := 1) (hP0 (level input r)) hAc hAd
      fun u hu => hle1 u hu.1 (lt_of_lt_of_le hu.2 (hPS (level input r)))
    have h' : P (level input r) ≤ L * w r := by
      rw [hwr]; exact min_le_left _ _
    linarith
  -- one band `I_W`
  have hband : ∀ e, A (P (e + 1)) - A (P e) ≤
      if (∀ q ∈ O, levelWeight e < w q) then levelLen input x r e else 0 := by
    intro e
    split_ifs with hc
    · have := sub_le_mul_of_deriv_right_le (c := 1) (hPmono e) hAc hAd
        fun u hu => hle1 u ((hP0 e).trans hu.1) (lt_of_lt_of_le hu.2 (hPS (e + 1)))
      rw [levelLen_eq_sub]
      simp only [hP] at this
      linarith
    · push_neg at hc
      obtain ⟨q, hq, hqe⟩ := hc
      have := sub_le_mul_of_deriv_right_le (c := 0) (hPmono e) hAc hAd fun u hu => by
        have huS : u < S := lt_of_lt_of_le hu.2 (hPS (e + 1))
        have hu0 : 0 ≤ u := (hP0 e).trans hu.1
        refine hle0 u hu0 huS q hq ?_
        have h1 : L * levelWeight e ≤ u := by
          rcases min_le_iff.mp hu.1 with h | h
          · exact h
          · exact absurd h (not_le.mpr huS)
        exact le_trans (mul_le_mul_of_nonneg_left hqe hL.le) h1
      linarith
  -- telescoping over the bands
  have htele : ∀ n, level input r ≤ n → A (P n) - A (P (level input r)) ≤
      ∑ e ∈ Finset.Icc (level input r) (n - 1),
        (if (∀ q ∈ O, levelWeight e < w q) then levelLen input x r e else 0) := by
    intro n hn
    induction n, hn using Int.le_induction with
    | base =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    | succ n hn ih =>
      have hins := Finset.insert_Icc_right_eq_Icc_add_one (a := level input r) (b := n - 1)
        (by omega)
      rw [sub_add_cancel] at hins
      rw [add_sub_cancel_right, ← hins, Finset.sum_insert (by simp)]
      have := hband n
      linarith
  have hM := le_maxLevel (input := input) r
  have hend : P (maxLevel input + 1) = S := by
    apply min_eq_right
    refine (serviceEnd_le hbv hx hr').trans (mul_le_mul_of_nonneg_left ?_ hL.le)
    rw [levelWeight_succ]; linarith [levelWeight_pos (maxLevel input)]
  have ht := htele (maxLevel input + 1) (by omega)
  rw [add_sub_cancel_right, hend] at ht
  rw [Finset.sum_filter]
  -- the page `r`
  have hgd : bregG δ = δ - 1 + L := by
    have := log_delta hbv
    unfold bregG; rw [this]; ring
  have hgx := bregG_nonneg (hx0 r)
  have hwr0 := hv.weight_pos r
  have hb1 : w r * bregG δ ≤ L * w r := by
    rw [hgd, mul_comm L]
    exact mul_le_mul_of_nonneg_left (by linarith [Instance.delta_lt_one hv]) hwr0.le
  have hb2 : 0 ≤ w r * bregG (x r) := mul_nonneg hwr0.le hgx
  rw [hD0, hD1]
  simp only [hrO, ↓reduceIte]
  linarith

end Phase

/-! ### One entry and one window -/

section Run

open scoped InstanceNotation

variable {input : Instance Page} (hv : input.Valid) {σ : Request Page → ℝ}
  (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
  (hSw : SwapForm input S)
include hv hσ hSw

/-- `prop:phaseD` at one entry: the change of the potential at entry `i`. -/
theorem entry_divergence_le (h2 : input.PowerOfTwoWeights) {i : ℕ}
    (hi : i < (log input).length) :
    divergence input (cacheAt input S (entryTime input i))
        (baseState (snapAt input (i + 1))) -
      divergence input (cacheAt input S (entryTime input i))
        (baseState (snapAt input i)) ≤
      -fetchAt input i + (1 + 2 * L) * missW input S i + excessAt input S i := by
  have hbv := hv
  cases hmv : moveAt i hi with
  | critical p =>
    obtain ⟨hidle, -, hsucc⟩ := critical_spec hv hi hmv
    obtain ⟨-, -, hxr, hr, -⟩ := critical_facts hv hi hmv
    have hx0 : (snapAt input i).x = baseState (snapAt input i) :=
      x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
    have hb1 : baseState (snapAt input (i + 1)) =
        criticalState input (snapAt input i).x p := by
      rw [hsucc]; rfl
    have hr' : δ < (snapAt input i).x p := hr
    have hO := Schedule.card_cacheAt hv hSw (entryTime input i)
    have hpf : fetchAt input i = criticalFetch input (snapAt input i).x p := by
      simp only [fetchAt, dif_pos hi, hmv]
    have hmw : missW input S i =
        if p ∈ cacheAt input S (entryTime input i) then 0
        else w p := by
      simp only [missW, dif_pos hi, hmv]
    rw [hb1, ← hx0, hpf, hmw]
    by_cases hrO : p ∈ cacheAt input S (entryTime input i)
    · have hex : excessAt input S i = 0 := by
        simp only [excessAt, dif_pos hi, hmv, if_pos hrO]
      rw [hex, if_pos hrO]
      have := critical_hit hbv hxr hr' hO hrO
      linarith
    · have hex : excessAt input S i =
          ∑ e ∈ excessLevels input S p (entryTime input i),
            levelLen input (snapAt input i).x p e := by
        simp only [excessAt, dif_pos hi, hmv, if_neg hrO]
      rw [hex, if_neg hrO]
      have := critical_miss_len hv h2 hxr hr hO hrO
      have := criticalFetch_lt_weight hbv hxr hr'
      unfold excessLevels
      have hL : 0 ≤ L := L_nonneg' input
      nlinarith
  | _ =>
    rw [baseState_succ_of_not_critical hv hi (by intro π hπ; rw [hmv] at hπ; cases hπ)]
    simp only [fetchAt, excessAt, missW, dif_pos hi, hmv]
    simp

/-- `lem:optmoves` between two entries: the comparator's steps in `(entryTime i, entryTime (i+1)]` change the potential by at most `L` times the evicted plus the fetched weight. -/
theorem window_divergence_le (i : ℕ) :
    divergence input (cacheAt input S (entryTime input (i + 1)))
          (baseState (snapAt input (i + 1))) -
        divergence input (cacheAt input S (entryTime input i))
          (baseState (snapAt input (i + 1))) ≤
      ∑ j ∈ range S.length,
        if ∃ h : j < S.length, entryTime input i < S[j].time ∧
            S[j].time ≤ entryTime input (i + 1) then
          L * ∑ q ∈ evictedAt input S j, w q +
            1 * ∑ p ∈ fetchedAt input S j, w p
        else 0 := by
  have hbv := hv
  have hx := (baseState_isRest hv (i + 1)).1
  have hF : ∀ (C : Finset Page) (p q : Page), p ∉ C → q ∈ C →
      divergence input (insert p (C.erase q)) (baseState (snapAt input (i + 1))) -
          divergence input C (baseState (snapAt input (i + 1))) ≤
        L * w q + 1 * w p := by
    intro C p q hp hq
    have hd := divergence_change_cache hbv hx C (insert p (C.erase q))
    have h1 : C \ insert p (C.erase q) ⊆ {q} := by
      intro a ha
      simp only [mem_sdiff, mem_insert, mem_erase] at ha
      simp only [mem_singleton]
      by_contra hne
      exact ha.2 (Or.inr ⟨hne, ha.1⟩)
    have h2 : insert p (C.erase q) \ C ⊆ {p} := by
      intro a ha
      simp only [mem_sdiff, mem_insert, mem_erase] at ha
      simp only [mem_singleton]
      rcases ha.1 with h | h
      · exact h
      · exact absurd h.2 ha.2
    have s1 : ∑ a ∈ C \ insert p (C.erase q), w a ≤ w q := by
      have := sum_le_sum_of_subset_of_nonneg h1 (fun a _ _ => (hv.weight_pos a).le)
      simpa using this
    have s2 : ∑ a ∈ insert p (C.erase q) \ C, w a ≤ w p := by
      have := sum_le_sum_of_subset_of_nonneg h2 (fun a _ _ => (hv.weight_pos a).le)
      simpa using this
    have := mul_le_mul_of_nonneg_left s1 (L_nonneg' input)
    linarith
  have hmono : entryTime input i ≤ entryTime input (i + 1) := entryTime_mono hv (by omega)
  have := cacheAt_change hv hSw
    (fun O => divergence input O (baseState (snapAt input (i + 1)))) L 1 hF hmono
  rw [sum_filter] at this
  exact this

/-- `prop:tele` (telescoping), against a comparator in swap form: `∑_λ fetch(λ) ≤ (L+1) fetchCost(S) + L w(C₀) + (L+1) ∑ w + (2L+1) ∑ missW + ∑ Exc`. -/
theorem fetchTotal_le (h2 : input.PowerOfTwoWeights) :
    fetchTotal input ≤
      (L + 1) * S.fetchCost input +
        L * ∑ p ∈ input.initialCache, w p +
        (L + 1) * input.totalWeight +
        (2 * L + 1) * ∑ i ∈ Finset.range (log input).length, missW input S i +
        ∑ i ∈ Finset.range (log input).length, excessAt input S i := by
  have hbv := hv
  have hL := L_nonneg' input
  set N := (log input).length with hN
  set D : ℕ → ℝ := fun i =>
    divergence input (cacheAt input S (entryTime input i))
      (baseState (snapAt input i)) with hD
  set D' : ℕ → ℝ := fun i =>
    divergence input (cacheAt input S (entryTime input i))
      (baseState (snapAt input (i + 1))) with hD'
  set g : ℕ → ℝ := fun j =>
    L * ∑ q ∈ evictedAt input S j, w q +
      1 * ∑ p ∈ fetchedAt input S j, w p with hg
  set W0 := ∑ p ∈ input.initialCache, w p with hW0
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    have h1 : 0 ≤ ∑ q ∈ evictedAt input S j, w q :=
      sum_nonneg fun q _ => (hv.weight_pos q).le
    have h2 : 0 ≤ ∑ q ∈ fetchedAt input S j, w q :=
      sum_nonneg fun q _ => (hv.weight_pos q).le
    simp only [hg]
    positivity
  -- the windows are disjoint
  have hdisj : ∑ i ∈ range N, ∑ j ∈ range S.length,
      (if ∃ h : j < S.length, entryTime input i < S[j].time ∧
          S[j].time ≤ entryTime input (i + 1) then g j else 0) ≤
      ∑ j ∈ range S.length, g j := by
    rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((range N).filter fun i => ∃ h : j < S.length,
        entryTime input i < S[j].time ∧ S[j].time ≤ entryTime input (i + 1)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      simp only [mem_filter] at ha hb
      obtain ⟨-, hj, ha1, ha2⟩ := ha
      obtain ⟨-, hj', hb1, hb2⟩ := hb
      by_contra hab
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · have : entryTime input (a + 1) ≤ entryTime input b := entryTime_mono hv (by omega)
        linarith
      · have : entryTime input (b + 1) ≤ entryTime input a := entryTime_mono hv (by omega)
        linarith
    have : ((((range N).filter fun i => ∃ h : j < S.length,
        entryTime input i < S[j].time ∧ S[j].time ≤ entryTime input (i + 1)).card : ℕ) : ℝ)
        ≤ 1 := by exact_mod_cast hcard
    nlinarith [hg0 j]
  have hgsum : ∑ j ∈ range S.length, g j ≤
      L * (S.fetchCost input + W0) + S.fetchCost input := by
    have hev := Schedule.sum_evicted_le hv hSw
    have hfe := Schedule.fetchCost_eq_sum_fetched hv hSw
    simp only [hg, sum_add_distrib, ← mul_sum, one_mul]
    rw [← hfe]
    have := mul_le_mul_of_nonneg_left hev hL
    linarith
  -- telescoping
  have htel : ∑ i ∈ range N, (D (i + 1) - D i) = D N - D 0 := sum_range_sub D N
  have hsplit : ∑ i ∈ range N, (D (i + 1) - D i) =
      ∑ i ∈ range N, (D' i - D i) + ∑ i ∈ range N, (D (i + 1) - D' i) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hphase : ∑ i ∈ range N, (D' i - D i) ≤
      ∑ i ∈ range N, (-fetchAt input i + (1 + 2 * L) * missW input S i +
        excessAt input S i) :=
    sum_le_sum fun i hi => entry_divergence_le hv hσ hSw h2 (mem_range.mp hi)
  have hwin : ∑ i ∈ range N, (D (i + 1) - D' i) ≤ ∑ j ∈ range S.length, g j :=
    le_trans (sum_le_sum fun i _ => window_divergence_le hv hσ hSw i) hdisj
  have hphase' : ∑ i ∈ range N, (-fetchAt input i +
      (1 + 2 * L) * missW input S i + excessAt input S i) =
      -fetchTotal input + (1 + 2 * L) * ∑ i ∈ range N, missW input S i +
        ∑ i ∈ range N, excessAt input S i := by
    rw [sum_add_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum]
    rfl
  have hD0 : D 0 ≤ (L + 1) * input.totalWeight :=
    divergence_le hbv (baseState_isRest hv 0).1 _
  have hDN : 0 ≤ D N := divergence_nonneg hbv (baseState_isRest hv N).1 _
  linarith

end Run

end TeleProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `Milestones.Prop17` -/
section

/-!
# Proposition 17: hit and miss potential changes

The platform's `potential` is the authors' `divergence`. The hit case is `critical_hit`. The miss
case is `TeleProof.critical_miss_len`, whose sum over integer levels `e` with
`w_p ≤ 2^e ≤ w_max`, `2^e < w_min(O)` of `levelLen` is the platform's `serviceExcess`
(a sum of `bandLength` over natural levels `j` with `w_p ≤ 2^j < w_min(O)`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PagingDelay.PMD.Bridge

open PagingDelay.PMD

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)

local notation "I" => inst n k hk hkn w hw

include hk hkn hw

lemma potential_eq (O : Finset (Fin n)) (y : Fin n → ℝ) :
    potential w O y = PagingWithDelay.PMD.divergence I O y := by
  unfold potential PagingWithDelay.PMD.divergence PagingWithDelay.PMD.bregG
  show _ = ∑ i, w i * (if i ∈ O then y i else (y i - 1 - Real.log (y i)))
  rw [← Finset.sum_sdiff (Finset.subset_univ O)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.mem_sdiff.1 hi).2]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos hi]

lemma pathFetch_eq (x : Fin n → ℝ) (p : Fin n) :
    pathFetch k w x p = PagingWithDelay.PMD.criticalFetch I x p := rfl

lemma bandLength_eq (S W : ℝ) (hS : 0 ≤ S) (hW : 0 ≤ W) :
    bandLength k S W = min (2 * (I).L * W) S - min ((I).L * W) S := by
  have hL : 0 ≤ (I).L := (PagingWithDelay.Instance.L_pos (valid hk hkn hw)).le
  rw [L_eq] at hL ⊢
  unfold bandLength
  have e : 2 * W * logFactor k = 2 * logFactor k * W := by ring
  rw [e, mul_comm W]
  have ha : 0 ≤ logFactor k * W := mul_nonneg hL hW
  rcases le_total S (logFactor k * W) with h | h
  · rw [min_eq_right h, min_eq_right (by linarith : S ≤ 2 * logFactor k * W)]
    simp only [sub_self]
    exact max_eq_left (by linarith [min_le_right (2 * logFactor k * W) S])
  · rw [min_eq_left h]
    exact max_eq_right (by
      rcases le_total S (2 * logFactor k * W) with h' | h'
      · rw [min_eq_right h']; linarith
      · rw [min_eq_left h']; linarith)

end

lemma bandLength_nonneg (k : ℕ) (S W : ℝ) : 0 ≤ bandLength k S W := le_max_left _ _

/-- `minWeight` of a nonempty set is the weight of one of its pages. -/
lemma exists_minWeight_eq {n : ℕ} (w : Fin n → ℝ) {O : Finset (Fin n)} (hO : O.Nonempty) :
    ∃ q ∈ O, minWeight w O = w q := by
  unfold minWeight
  suffices h : ∀ l : List (Fin n), l ≠ [] → ∃ q ∈ l, ((l.map w).foldr
      (fun a z => some (match z with | none => a | some b => min a b)) none).getD 0 = w q by
    obtain ⟨q, hq, h⟩ := h O.toList (by simpa using hO.ne_empty)
    exact ⟨q, Finset.mem_toList.1 hq, h⟩
  intro l hl
  induction l with
  | nil => exact absurd rfl hl
  | cons x l ih =>
    simp only [List.map_cons, List.foldr_cons, Option.getD_some]
    split
    · next heq => exact ⟨x, by simp, rfl⟩
    · next b heq =>
      have hl' : l ≠ [] := by
        rintro rfl
        simp at heq
      obtain ⟨q, hq, hqb⟩ := ih hl'
      rw [heq, Option.getD_some] at hqb
      rcases min_choice (w x) b with h | h
      · exact ⟨x, by simp, h⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq, h.trans hqb⟩

/-- Platform levels: `j` with `2^j ≤ w_max` lies in `levels w`. -/
lemma mem_levels {n : ℕ} {w : Fin n → ℝ} (hw : DyadicWeights w) {j : ℕ} (i : Fin n)
    (hj : (2 : ℝ) ^ j ≤ w i) : j ∈ levels w := by
  obtain ⟨m, hm⟩ := hw i
  have hjm : j ≤ m := by
    rw [hm] at hj
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hj
  have hfl : ⌊Real.log (max 1 (w i)) / Real.log 2⌋₊ = m := by
    rw [hm, max_eq_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)), Real.log_pow,
      mul_div_assoc, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one,
      Nat.floor_natCast]
  unfold levels
  rw [List.mem_range]
  have := Finset.le_sup (f := fun i => ⌊Real.log (max 1 (w i)) / Real.log 2⌋₊)
    (Finset.mem_univ i)
  simp only [hfl] at this
  omega

/-- **Proposition 17** (`prop:phaseD`). -/
theorem prop17 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) (O : Finset (Fin n)) (hO : O.card = k) :
    let Δ := potential w O (pathEnd k w x p) - potential w O x
    (p ∈ O → Δ ≤ -pathFetch k w x p) ∧
    (p ∉ O → Δ ≤ 2 * logFactor k * w p + serviceExcess k w x p O) := by
  intro Δ
  have hw' := weight_pos_of_PMDWeights hw
  have hv := valid hk hkn hw'
  have hxr := (isRest_iff hk hkn hw' x).2 hx
  have hL : 0 ≤ logFactor k := (PagingWithDelay.Instance.L_pos hv).le
  have hexc0 : 0 ≤ serviceExcess k w x p O := by
    unfold serviceExcess
    exact List.sum_nonneg fun a ha => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      exact bandLength_nonneg _ _ _
  have hΔ : Δ = PagingWithDelay.PMD.divergence (inst n k hk hkn w hw') O
      (PagingWithDelay.PMD.criticalState (inst n k hk hkn w hw') x p) -
      PagingWithDelay.PMD.divergence (inst n k hk hkn w hw') O x := by
    simp only [Δ]
    rw [potential_eq hk hkn hw', potential_eq hk hkn hw', pathEnd_eq hk hkn hw' hx]
  rcases eq_or_lt_of_le (hx.1 p).1 with h | h
  · -- `x_p = δ`: nothing happens
    have hc := PagingWithDelay.PMD.criticalState_eq_of_le hxr (le_of_eq h.symm)
    rw [hΔ, hc, sub_self]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · simp [pathFetch, ← h]
    · have := hw' p
      positivity
  refine ⟨fun hpO => ?_, fun hpO => ?_⟩
  · rw [hΔ, pathFetch_eq hk hkn hw']
    exact PagingWithDelay.PMD.critical_hit hv hxr h hO hpO
  · have h2 : (inst n k hk hkn w hw').PowerOfTwoWeights := fun i => by
      obtain ⟨m, hm⟩ := hw.1 i
      exact ⟨m, by simp [inst, hm]⟩
    have hmiss := PagingWithDelay.PMD.TeleProof.critical_miss_len hv h2 hxr h hO hpO
    rw [hΔ]
    refine hmiss.trans (add_le_add (le_of_eq rfl) ?_)
    set I' := inst n k hk hkn w hw' with hI'
    set S := PagingWithDelay.PMD.serviceEnd I' x p with hS
    have hS0 : 0 ≤ S := PagingWithDelay.PMD.serviceEnd_nonneg hv hxr h
    have hpl : pathLength k w x p = S := pathLength_eq hk hkn hw' hx p
    suffices key : ∀ E : Finset ℤ, (∀ e ∈ E, e ∈ Finset.Icc (PagingWithDelay.PMD.level I' p)
        (PagingWithDelay.PMD.maxLevel I') ∧
          ∀ q ∈ O, PagingWithDelay.PMD.levelWeight e < I'.weight q) →
        ∑ e ∈ E, PagingWithDelay.PMD.levelLen I' x p e ≤ serviceExcess k w x p O from
      key _ fun e he => by simpa only [Finset.mem_filter] using he
    intro E hEmem
    set L' := (levels w).filter (fun j => decide (w p ≤ level j ∧ level j < minWeight w O))
      with hL'
    have hnd : L'.Nodup := by
      unfold levels at hL'
      rw [hL']
      exact List.nodup_range.filter _
    -- all levels in `E` are nonnegative, as `w_p ≥ 1`
    have hE0 : ∀ e ∈ E, 0 ≤ e := by
      intro e he
      have h1 := (Finset.mem_Icc.1 (hEmem e he).1).1
      refine le_trans ?_ h1
      by_contra hneg
      push_neg at hneg
      have h3 : w p ≤ PagingWithDelay.PMD.levelWeight (-1) :=
        (PagingWithDelay.PMD.level_le_iff hv p (-1)).1 (by omega)
      obtain ⟨m, hm⟩ := hw.1 p
      have hm1 : (1 : ℝ) ≤ w p := by rw [hm]; exact one_le_pow₀ (by norm_num)
      have h4 : PagingWithDelay.PMD.levelWeight (-1) = 1 / 2 := by
        unfold PagingWithDelay.PMD.levelWeight; norm_num
      linarith
    have hz : ∀ e : ℤ, 0 ≤ e → PagingWithDelay.PMD.levelWeight e = level e.toNat := by
      intro e he
      unfold PagingWithDelay.PMD.levelWeight level
      rw [← zpow_natCast, Int.toNat_of_nonneg he]
    have hOne : O.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨qmin, hqmin, hmin⟩ := exists_minWeight_eq w hOne
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨imax, himax⟩ := exists_eq_ciSup_of_finite (f := PagingWithDelay.PMD.level I')
    have hsub : E.image Int.toNat ⊆ L'.toFinset := by
      intro j hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hj
      have he0 := hE0 e he
      obtain ⟨heIcc, heO⟩ := hEmem e he
      obtain ⟨h1, h2'⟩ := Finset.mem_Icc.1 heIcc
      rw [List.mem_toFinset, hL', List.mem_filter]
      refine ⟨mem_levels hw.1 imax ?_, ?_⟩
      · rw [← level, ← hz e he0]
        have := PagingWithDelay.PMD.levelWeight_level hv h2 imax
        refine le_trans ?_ (le_of_eq this)
        unfold PagingWithDelay.PMD.levelWeight
        exact zpow_le_zpow_right₀ (by norm_num) (by
          rw [himax]; exact h2')
      · simp only [decide_eq_true_eq]
        rw [← hz e he0, hmin]
        exact ⟨(PagingWithDelay.PMD.level_le_iff hv p e).1 h1, heO qmin hqmin⟩
    calc ∑ e ∈ E, PagingWithDelay.PMD.levelLen I' x p e
        = ∑ e ∈ E, bandLength k S (level e.toNat) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [bandLength_eq hk hkn hw' S _ hS0 (by unfold level; positivity), ← hz e (hE0 e he)]
          rfl
      _ = ∑ j ∈ E.image Int.toNat, bandLength k S (level j) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have := hE0 a ha
          have := hE0 b hb
          omega
      _ ≤ ∑ j ∈ L'.toFinset, bandLength k S (level j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => bandLength_nonneg _ _ _
      _ = (L'.map fun j => bandLength k S (level j)).sum := List.sum_toFinset _ hnd
      _ = serviceExcess k w x p O := by
          unfold serviceExcess
          rw [hpl]

end PagingDelay.PMD.Bridge
end

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) (O : Finset (Fin n)) (hO : O.card = k) :
    let Δ := potential w O (pathEnd k w x p) - potential w O x
    (p ∈ O → Δ ≤ -pathFetch k w x p) ∧
    (p ∉ O → Δ ≤ 2 * logFactor k * w p + serviceExcess k w x p O) :=
  PagingDelay.PMD.Bridge.prop17 n k hk hkn w hw x hx p O hO
