-- Prove2me | solution 1 for PagingDelay.PMD.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-14T08:45:45.823509+00:00
-- url     : https://prove2.me/submissions/ed3a8e7f-6b93-4479-be56-70740878b099

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

/-! ## Inlined from `Milestones.Lemma5` -/
section

/-!
# Lemma 5: `|λ| ≤ 3 EV(λ)`

The platform defines the weighted eviction as `∫₀^{|λ|} ∑ᵢ wᵢ (dλᵢ/ds)⁺ ds` (with Lean's junk value
`0` for the derivative at the finitely many kinks). Away from the kinks, the integrand is the
right derivative `evDeriv` of the authors' weighted missing mass `evMass`, so the integral is
`evMass(|λ|) - evMass(0) = criticalEV` (`lem:clock` then gives the bound).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PagingDelay.PMD.Bridge

open PagingDelay.PMD MeasureTheory Set

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)

local notation "I" => inst n k hk hkn w hw

include hk hkn hw

/-- The two-sided derivative of an eviction curve away from its kink. -/
lemma hasDerivAt_evictCurve {x : Fin n → ℝ} {i : Fin n} {u : ℝ}
    (hu : x i * Real.exp (u / w i) ≠ 1) :
    HasDerivAt (PagingWithDelay.PMD.evictCurve I x i)
      (if PagingWithDelay.PMD.NotEvicted I x i u then
        PagingWithDelay.PMD.evictCurve I x i u / w i else 0) u := by
  have hc : Continuous fun s => x i * Real.exp (s / w i) := by fun_prop
  rcases lt_or_gt_of_ne hu with h | h
  · have hNE : PagingWithDelay.PMD.NotEvicted I x i u := h
    rw [if_pos hNE]
    have hd : HasDerivAt (fun s => x i * Real.exp (s / w i))
        (x i * Real.exp (u / w i) / w i) u := by
      have := (((hasDerivAt_id u).div_const (w i)).exp).const_mul (x i)
      refine this.congr_deriv ?_
      simp only [id]
      ring
    have hev : PagingWithDelay.PMD.evictCurve I x i =ᶠ[nhds u]
        fun s => x i * Real.exp (s / w i) := by
      filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with s hs
      exact min_eq_right hs.le
    rw [PagingWithDelay.PMD.dvEvictCurve_of_notEvicted hNE]
    exact hd.congr_of_eventuallyEq hev
  · have hNE : ¬ PagingWithDelay.PMD.NotEvicted I x i u := not_lt.2 h.le
    rw [if_neg hNE]
    have hev : PagingWithDelay.PMD.evictCurve I x i =ᶠ[nhds u] fun _ => (1 : ℝ) := by
      filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with s hs
      exact min_eq_left hs.le
    exact (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hev

/-- The kinks of the eviction curves form a countable set. -/
lemma countable_kinks {x : Fin n → ℝ} (hx0 : ∀ i, 0 < x i) :
    (⋃ i, {u : ℝ | x i * Real.exp (u / w i) = 1}).Countable := by
  refine Set.countable_iUnion fun i => Set.Subsingleton.countable ?_
  intro a ha b hb
  have h : x i * Real.exp (a / w i) = x i * Real.exp (b / w i) := ha.trans hb.symm
  have h' := Real.exp_injective (mul_left_cancel₀ (hx0 i).ne' h)
  field_simp [(hw i).ne'] at h'
  exact h'

/-- Away from the kinks, the platform's integrand is `evDeriv`. -/
lemma integrand_eq {x : Fin n → ℝ} (hx0 : ∀ i, 0 < x i) (p : Fin n) {u : ℝ}
    (hu : u ∉ ⋃ i, {u : ℝ | x i * Real.exp (u / w i) = 1}) :
    ∑ i, w i * max 0 (deriv (fun t => path k w x p t i) u) =
      PagingWithDelay.PMD.evDeriv I x p u := by
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hu
  set g : Fin n → ℝ := fun j => if PagingWithDelay.PMD.NotEvicted I x j u then
    PagingWithDelay.PMD.evictCurve I x j u / w j else 0 with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [hg]
    split_ifs
    · exact div_nonneg (PagingWithDelay.PMD.dvEvictCurve_pos (hx0 j) u).le (hw j).le
    · exact le_rfl
  have hd : ∀ j, HasDerivAt (PagingWithDelay.PMD.evictCurve I x j) (g j) u :=
    fun j => hasDerivAt_evictCurve hk hkn hw (hu j)
  have hpath : ∀ i, (fun t => path k w x p t i) =
      fun t => PagingWithDelay.PMD.mdPath I x p t i := fun i => by
    rw [path_eq hk hkn hw]
  -- the page `p` contributes `0`
  have hp : max 0 (deriv (fun t => path k w x p t p) u) = 0 := by
    rw [hpath p]
    have hdp : HasDerivAt (fun t => PagingWithDelay.PMD.mdPath I x p t p)
        (0 - ∑ j ∈ Finset.univ.erase p, g j) u := by
      have := (hasDerivAt_const u (PagingWithDelay.PMD.restMass I)).sub
        (HasDerivAt.fun_sum (u := Finset.univ.erase p) fun j _ => hd j)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      exact PagingWithDelay.PMD.mdPath_self x p t
    rw [hdp.deriv]
    exact max_eq_left (by linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ.erase p) => hg0 j])
  -- the other pages contribute `wᵢ gᵢ`
  have hi : ∀ i ∈ Finset.univ.erase p, w i * max 0 (deriv (fun t => path k w x p t i) u) =
      (if PagingWithDelay.PMD.NotEvicted I x i u then
        PagingWithDelay.PMD.evictCurve I x i u else 0) := fun i hi' => by
    have hne := Finset.ne_of_mem_erase hi'
    rw [hpath i]
    have he : (fun t => PagingWithDelay.PMD.mdPath I x p t i) =
        PagingWithDelay.PMD.evictCurve I x i := by
      funext t
      exact PagingWithDelay.PMD.mdPath_of_ne x p t hne
    rw [he, (hd i).deriv, max_eq_right (hg0 i)]
    simp only [hg]
    split_ifs
    · field_simp [(hw i).ne']
    · simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), hp, mul_zero, zero_add,
    Finset.sum_congr rfl hi]
  rfl

lemma intervalIntegrable_evDeriv (x : Fin n → ℝ) (p : Fin n) (a b : ℝ) :
    IntervalIntegrable (PagingWithDelay.PMD.evDeriv I x p) volume a b := by
  have hsum : PagingWithDelay.PMD.evDeriv I x p = ∑ i ∈ Finset.univ.erase p,
      (fun u => if PagingWithDelay.PMD.NotEvicted I x i u then
        PagingWithDelay.PMD.evictCurve I x i u else 0) := by
    funext u
    simp only [PagingWithDelay.PMD.evDeriv, Finset.sum_apply]
  rw [hsum]
  refine IntervalIntegrable.sum _ fun i _ => ?_
  have hc : Continuous fun s => x i * Real.exp (s / w i) := by fun_prop
  have hmeas : MeasurableSet {u : ℝ | x i * Real.exp (u / w i) < 1} :=
    (isOpen_lt hc continuous_const).measurableSet
  have heq : (fun u => if PagingWithDelay.PMD.NotEvicted I x i u then
      PagingWithDelay.PMD.evictCurve I x i u else 0) =
      {u : ℝ | x i * Real.exp (u / w i) < 1}.indicator
        (PagingWithDelay.PMD.evictCurve I x i) := by
    funext u
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rfl
  rw [heq]
  refine IntegrableOn.intervalIntegrable ?_
  exact ((PagingWithDelay.PMD.dvEvictCurve_continuous (input := I) x i).continuousOn.integrableOn_compact
    isCompact_uIcc).indicator hmeas

end

/-- **Lemma 5** (`lem:clock`): `|λ| ≤ 3 EV(λ)`. -/
theorem lemma5 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) :
    pathLength k w x p ≤ 3 * weightedEviction k w x p := by
  have hw' := weight_pos_of_PMDWeights hw
  have hv := valid hk hkn hw'
  have hxr := (isRest_iff hk hkn hw' x).2 hx
  have hd0 : 0 < delta k := PagingWithDelay.Instance.delta_pos hv
  have hx0 : ∀ i, 0 < x i := fun i => hd0.trans_le (hx.1 i).1
  unfold weightedEviction
  rw [pathLength_eq hk hkn hw' hx]
  rcases eq_or_lt_of_le (hx.1 p).1 with h | h
  · rw [PagingWithDelay.PMD.serviceEnd_eq_zero_of_le hxr (le_of_eq h.symm)]
    simp
  set S := PagingWithDelay.PMD.serviceEnd (inst n k hk hkn w hw') x p with hS
  have hS0 : 0 ≤ S := PagingWithDelay.PMD.serviceEnd_nonneg hv hxr h
  have hint : ∫ s in (0 : ℝ)..S, ∑ i, w i * max 0 (deriv (fun t => path k w x p t i) s) =
      ∫ s in (0 : ℝ)..S, PagingWithDelay.PMD.evDeriv (inst n k hk hkn w hw') x p s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_kinks hk hkn hw' hx0).ae_notMem volume] with u hu _
    exact integrand_eq hk hkn hw' hx0 p hu
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hS0
    (PagingWithDelay.PMD.continuous_evMass x p).continuousOn
    (fun u _ => (PagingWithDelay.PMD.hasDerivWithinAt_evMass hv hx0 p u).mono Ioi_subset_Ici_self)
    (intervalIntegrable_evDeriv hk hkn hw' x p 0 S)
  rw [hint, hftc, ← PagingWithDelay.PMD.criticalEV_eq_evMass hv hxr h]
  exact PagingWithDelay.PMD.serviceEnd_le_three_mul_criticalEV hv hxr h

end PagingDelay.PMD.Bridge
end

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) :
    pathLength k w x p ≤ 3 * weightedEviction k w x p :=
  PagingDelay.PMD.Bridge.lemma5 n k hk hkn w hw x hx p
