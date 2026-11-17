-- Prove2me | solution 1 for PagingDelay.PMD.proposition_30
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-16T13:52:37.503797+00:00
-- url     : https://prove2.me/submissions/3232fc86-1ee8-4afe-a31d-429d4aa67e1c

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
import Definitions.Def_PagingDelay_PMD_Model
import Definitions.Def_PagingDelay_PMD_Path
import Definitions.Def_PagingDelay_PMD_Algorithm

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

/-- An instance: positive page weights, a cache size `0 < k < n`, the initial cache `C₀` of `k` pages, a page `i₀ ∉ C₀` (`startPage`, the page holding missing mass `1 - kδ` in the initial fractional state), a rank `tieRank` breaking ties between pages (lower rank first), and a finite list of requests. The order of the list only breaks ties between simultaneous choices. -/
structure Instance (Page : Type*) [Fintype Page] where
  weight : Page → ℝ
  weight_pos : ∀ p, 0 < weight p
  cacheSize : ℕ
  cacheSize_pos : 0 < cacheSize
  cacheSize_lt : cacheSize < Fintype.card Page
  initialCache : Finset Page
  initialCache_card : initialCache.card = cacheSize
  startPage : Page
  startPage_not_mem : startPage ∉ initialCache
  tieRank : Page → ℕ
  requests : List (Request Page)

namespace Instance

variable {Page : Type*} [Fintype Page]

/-- The total weight `∑ᵢ wᵢ` of all pages. -/
noncomputable def totalWeight (input : Instance Page) : ℝ :=
  ∑ p, input.weight p

/-- The instance as known at time `t`: the requests that have arrived by `t` (with their delay functions); weights, cache size, initial cache, start page and tie ranks are known from the start. -/
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
1. If some page is critical at `now`, the first such page `p` (in the tie order `pageOrder`, by `tieRank`) gets a **critical service** `λ`: every page `q` with `w_q ≤ w_p` raises `c_q` by the same fraction `θ` of its overshoot, `|λ| / L` in total; `x ← λ(|λ|)`; all pending requests on `p` are served and `c_p ← 0`; and `|λ|_W = |I_W ∩ [0, |λ|]|` with `I_W = [L W, 2 L W)` is deposited into `B_W` for every level `W ≥ w_p`. Then the levels `W = w_min, 2 w_min, …, w_max` are examined in increasing order; a **level-`W` preemptive service** runs if `B_W ≥ 4W` and the pages of weight `≤ W` hold cached mass at least `1 - δ`: it opens a hole (every page of weight `≤ W` gives up the same fraction of its cached mass, `1 - δ` in total) and pays `W (1 - δ)` from `B_W`; while `B_W ≥ W`, it performs a round trip (`x_q ← δ`, then back) on the pending page `q` of weight `≤ W` with the earliest deadline `inf {τ ≥ t : delay_q(τ) > w_q}`, serving all pending requests on `q`, resetting `c_q` and paying `w_q (x_q - δ)`; finally it closes the hole.
2. Otherwise the loop advances to the infimum of the times `≥ now` at which `eq:trigger` holds for some page (some page is critical there, and it is later than `now`), unless the next arrival comes no later; then it advances to that arrival time, where its requests arrive. A request on a page with `x_p = δ` is served on arrival.

The loop is a deterministic state machine `next`. Every move records the waypoints of the fractional schedule (`waypoints`): the state after a critical service, after opening a hole, at the bottom of a round trip and after it, and after closing the hole (the states `x⁽ᵛ⁾` of `sec:length`). Ticks and advances record the unchanged state at their time.

**Differences from the paper.**
* *Ties* (several pages critical at once, equal deadlines) are broken by the ranks `tieRank` of the pages (then by a fixed order of the pages and by the order of the pending requests).
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

/-- The page outside `C₀` that holds missing mass `1 - kδ` in the initial state: the start page `i₀` of the instance. -/
def initialPage : Option Page :=
  some input.startPage

/-- The pages in the tie order: sorted by `tieRank` (stable, so pages of equal rank keep the order of `Finset.univ.toList`). -/
def pageOrder : List Page :=
  Finset.univ.toList.mergeSort fun a b => decide (input.tieRank a ≤ input.tieRank b)

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

/-- The next round trip of a level-`W` preemptive service at time `t`: the pending request on a page of weight `≤ W` whose page has the earliest deadline, ties broken by the smaller `tieRank` of the page (and then by the pending list). -/
def tripCandidate (pending : List (Request Page)) (t : ℝ) (e : ℤ) : Option (Request Page) :=
  (pending.filter fun ρ => decide (level input ρ.page ≤ e)).argmin
    fun ρ => toLex (pageDeadline input pending t ρ.page, input.tieRank ρ.page)

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

/-- The page served by the next critical service at time `s.now`: the first page in the tie order `pageOrder` that is critical at `s.now`. -/
def triggerPage (s : Snap Page) : Option Page :=
  (pageOrder input).find? fun p => decide (Critical input s.x s.pending s.claims s.now p)

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
    ∃ p₀, initialPage input = some p₀ ∧ p₀ ∉ input.initialCache :=
  ⟨input.startPage, rfl, input.startPage_not_mem⟩

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

/-! ## Inlined from `PagingWithDelay.Run.SortedTimes` -/
section

/-!
# Lists of times filtered up to a time

Two facts about sorted lists of times and their prefixes up to `t`, used to show that `PMD` is online (`PagingWithDelay/Run/Online.lean`).
-/

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OnlineProof

theorem filter_le_nil (t b : ℝ) (r : List ℝ) (h : (b :: r).Pairwise (· ≤ ·)) (hb : t < b) :
    (b :: r).filter (fun a => decide (a ≤ t)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha
  have : b ≤ a := by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (List.pairwise_cons.mp h).1 a ha
  simp only [decide_eq_true_eq, not_le]
  linarith

theorem heads (t : ℝ) {u1 u2 : List ℝ} (h1 : u1.Pairwise (· ≤ ·)) (h2 : u2.Pairwise (· ≤ ·))
    (hf : u1.filter (fun a => decide (a ≤ t)) = u2.filter (fun a => decide (a ≤ t))) :
    ((∀ a ∈ u1.head?, t < a) ∧ (∀ a ∈ u2.head?, t < a)) ∨
      ∃ a r1 r2, a ≤ t ∧ u1 = a :: r1 ∧ u2 = a :: r2 ∧
        r1.filter (fun a => decide (a ≤ t)) = r2.filter (fun a => decide (a ≤ t)) := by
  cases u1 with
  | nil =>
    cases u2 with
    | nil => left; simp
    | cons b r2 =>
      left
      refine ⟨by simp, ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      by_contra hb
      push_neg at hb
      simp [hb] at hf
  | cons a r1 =>
    cases u2 with
    | nil =>
      left
      refine ⟨?_, by simp⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      by_contra ha
      push_neg at ha
      simp [ha] at hf
    | cons b r2 =>
      by_cases ha : a ≤ t
      · by_cases hb : b ≤ t
        · right
          simp only [List.filter_cons, ha, hb, decide_true, if_true, List.cons.injEq] at hf
          obtain ⟨rfl, hr⟩ := hf
          exact ⟨a, r1, r2, ha, rfl, rfl, hr⟩
        · exfalso
          rw [filter_le_nil t b r2 h2 (lt_of_not_ge hb)] at hf
          simp [ha] at hf
      · by_cases hb : b ≤ t
        · exfalso
          rw [filter_le_nil t a r1 h1 (lt_of_not_ge ha)] at hf
          simp [hb] at hf
        · left
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
          exact ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩

end OnlineProof

end

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Run.Online` -/
section

/-!
# `PMD` for paging with delay is online

A self-contained simulation argument (with the facts about sorted lists of times of `Run/SortedTimes.lean`).

* **Termination.** The measure `meas` strictly decreases along a run: ticks consume an arrival time, critical services and round trips remove a pending request (`eq:trigger` forces `o_p > 0`, hence a pending request on `p`, as `c_p ≥ 0`), the level loop decreases the rank of the stage, and an `advance` is always followed by a critical service (with finitely many pages, some page is critical at the infimum of the trigger times). The initial measure is below `fuel`, so the run stops before fuel runs out and the output does not depend on the amount of fuel (`run_indep`).
* **Simulation.** Two runs on instances that agree up to time `t` make the same moves while `now ≤ t`; once one would move past `t` (an advance to a trigger time `> t`, or a tick at an arrival `> t`), both record only waypoints after `t`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage)

noncomputable section

namespace OnlineProof

/-! ### Instances with the same weights, cache size and initial cache -/

/-- Two instances with the same weights, cache size, initial cache, start page and tie ranks. -/
def Same (I1 I2 : Instance Page) : Prop :=
  I1.weight = I2.weight ∧ I1.cacheSize = I2.cacheSize ∧ I1.initialCache = I2.initialCache ∧
    I1.startPage = I2.startPage ∧ I1.tieRank = I2.tieRank

variable {I1 I2 : Instance Page}

theorem Same.eq (h : Same I1 I2) : I1 = { I2 with requests := I1.requests } := by
  obtain ⟨w, hw, k, hk, hkn, C, hC, i₀, hi₀, π, r⟩ := I1
  obtain ⟨w', hw', k', hk', hkn', C', hC', i₀', hi₀', π', r'⟩ := I2
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  try dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem Same.criticalState (h : Same I1 I2) :
    (criticalState I1 : (Page → ℝ) → Page → Page → ℝ) = criticalState I2 := by rw [h.eq]; rfl
theorem Same.minLevel (h : Same I1 I2) : minLevel I1 = minLevel I2 := by rw [h.eq]; rfl
theorem Same.hole (h : Same I1 I2) : (hole I1 : (Page → ℝ) → ℤ → Page → ℝ) = hole I2 := by
  rw [h.eq]; rfl
theorem Same.holePayment (h : Same I1 I2) : (holePayment I1 : ℤ → ℝ) = holePayment I2 := by
  rw [h.eq]; rfl
theorem Same.preemptCondition (h : Same I1 I2) :
    (preemptCondition I1 : (Page → ℝ) → (ℤ → ℝ) → ℤ → Prop) = preemptCondition I2 := by
  rw [h.eq]; rfl
theorem Same.afterLevel (h : Same I1 I2) : (afterLevel I1 : ℤ → Stage Page) = afterLevel I2 := by
  rw [h.eq]; rfl
theorem Same.tripCost (h : Same I1 I2) : (tripCost I1 : (Page → ℝ) → Page → ℝ) = tripCost I2 := by
  rw [h.eq]; rfl
theorem Same.initialState (h : Same I1 I2) : (initialState I1 : Page → ℝ) = initialState I2 := by
  rw [h.eq]; rfl
theorem Same.delta (h : Same I1 I2) : I1.delta = I2.delta := by rw [h.eq]; rfl
theorem Same.triggerPage (h : Same I1 I2) :
    (triggerPage I1 : Snap Page → Option Page) = triggerPage I2 := by rw [h.eq]; rfl
theorem Same.triggerTimes (h : Same I1 I2) :
    (triggerTimes I1 : Snap Page → Set ℝ) = triggerTimes I2 := by rw [h.eq]; rfl
theorem Same.claimUpdate (h : Same I1 I2) :
    (claimUpdate I1 : (Page → ℝ) → List (Request Page) → (Page → ℝ) → ℝ → Page → Page → ℝ) =
      claimUpdate I2 := by rw [h.eq]; rfl
theorem Same.deposit (h : Same I1 I2) :
    (deposit I1 : (Page → ℝ) → Page → (ℤ → ℝ) → ℤ → ℝ) = deposit I2 := by rw [h.eq]; rfl
theorem Same.tripCandidate (h : Same I1 I2) :
    (tripCandidate I1 : List (Request Page) → ℝ → ℤ → Option (Request Page)) =
      tripCandidate I2 := by rw [h.eq]; rfl

/-! ### The moves of `next` -/

section Moves

variable (input : Instance Page) {s : Snap Page}

theorem next_critical {q : Page} (hst : s.stage = .idle) (htp : triggerPage input s = some q) :
    next input s = some (.critical q,
      { s with
        x := criticalState input s.x q
        budget := deposit input s.x q s.budget
        pending := s.pending.filter fun π => decide (π.page ≠ q)
        claims := Function.update (claimUpdate input s.x s.pending s.claims s.now q) q 0
        stage := .examine (minLevel input) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, htp]

theorem next_advance (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : (triggerTimes input s).Nonempty ∧ ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a) :
    next input s = some (.advance (sInf (triggerTimes input s)),
      { s with now := sInf (triggerTimes input s) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, htp]
  rw [if_pos hc]

open scoped InstanceNotation in
theorem next_tick {a : ℝ} {r : List ℝ} (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a))
    (hup : s.upcoming = a :: r) :
    next input s = some (.tick a,
      { s with
        now := a
        upcoming := r
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst hup
  subst hst hup
  simp only [next, htp]
  rw [if_neg hc]

theorem next_none (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a))
    (hup : s.upcoming = []) :
    next input s = none := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst hup
  subst hst hup
  simp only [next, htp]
  rw [if_neg hc]

theorem next_openHole {e : ℤ} (hst : s.stage = .examine e)
    (hpc : preemptCondition input s.x s.budget e) :
    next input s = some (.openHole e,
      { s with
        x := hole input s.x e
        budget := Function.update s.budget e (s.budget e - holePayment input e)
        stage := .preempt e s.x }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, if_pos hpc]

theorem next_skip {e : ℤ} (hst : s.stage = .examine e)
    (hpc : ¬ preemptCondition input s.x s.budget e) :
    next input s = some (.skip e, { s with stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, if_neg hpc]

theorem next_closeNone {e : ℤ} {base : Page → ℝ} (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = none) :
    next input s = some (.closeHole e none,
      { s with x := base, stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, htc]

theorem next_trip {e : ℤ} {base : Page → ℝ} {π : Request Page} (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = some π)
    (hcost : levelWeight e ≤ s.budget e) :
    next input s = some (.trip e π,
      { s with
        budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
        pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
        claims := Function.update s.claims π.page 0 }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, htc, if_pos hcost]

theorem next_closeSome {e : ℤ} {base : Page → ℝ} {π : Request Page}
    (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = some π)
    (hcost : ¬ levelWeight e ≤ s.budget e) :
    next input s = some (.closeHole e (some π),
      { s with x := base, stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  try dsimp only at hst
  subst hst
  simp only [next, htc, if_neg hcost]

end Moves

/-! ### The trigger -/

section Trigger

variable (input : Instance Page)

theorem critical_of_triggerPage {s : Snap Page} {q : Page} (h : triggerPage input s = some q) :
    Critical input s.x s.pending s.claims s.now q := by
  have := List.find?_some h
  simpa using this

theorem pageDelay_eq_zero (L : List (Request Page)) (q : Page) (τ : ℝ)
    (h : ∀ ρ ∈ L, ρ.page ≠ q) : pageDelay L q τ = 0 := by
  have : L.filter (fun ρ => decide (ρ.page = q)) = [] :=
    List.filter_eq_nil_iff.mpr fun ρ hρ => by simpa using h ρ hρ
  simp [pageDelay, this]

/-- `eq:trigger` needs a pending request on the page (claims are nonnegative). -/
theorem exists_pending_of_triggerCond (hv : input.Valid) {x : Page → ℝ} {L : List (Request Page)}
    {c : Page → ℝ} {τ : ℝ} {q : Page} (hc : ∀ q, 0 ≤ c q) (h : TriggerCond input x L c τ q) :
    ∃ ρ ∈ L, ρ.page = q := by
  by_contra hne
  push_neg at hne
  have h1 := h.1
  unfold overshoot at h1
  rw [pageDelay_eq_zero L q τ hne] at h1
  have := hv.weight_pos q
  have := hc q
  exact absurd h1 (not_lt.mpr (max_le le_rfl (by linarith)))

/-- A critical page has a pending request. -/
theorem exists_pending_of_critical (hv : input.Valid) {x : Page → ℝ} {L : List (Request Page)}
    {c : Page → ℝ} {τ : ℝ} {q : Page} (hc : ∀ q, 0 ≤ c q) (h : Critical input x L c τ q) :
    ∃ ρ ∈ L, ρ.page = q := by
  obtain ⟨τ', -, -, h'⟩ := h 1 one_pos
  exact exists_pending_of_triggerCond input hv hc h'

theorem not_triggerCond_nil (hv : input.Valid) {x : Page → ℝ} {c : Page → ℝ} {τ : ℝ} {q : Page}
    (hc : ∀ q, 0 ≤ c q) : ¬ TriggerCond input x [] c τ q := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := exists_pending_of_triggerCond input hv hc h
  simp at hρ

theorem not_critical_nil (hv : input.Valid) {x : Page → ℝ} {c : Page → ℝ} {τ : ℝ} {q : Page}
    (hc : ∀ q, 0 ≤ c q) : ¬ Critical input x [] c τ q := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := exists_pending_of_critical input hv hc h
  simp at hρ

/-- Some page is critical at the infimum of the trigger times: with finitely many pages, `eq:trigger` holds for one of them at times arbitrarily close after the infimum. -/
theorem exists_critical_sInf {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    ∃ p, Critical input s.x s.pending s.claims (sInf (triggerTimes input s)) p := by
  have hbdd : BddBelow (triggerTimes input s) := ⟨s.now, fun _ ht => ht.1⟩
  by_contra hno
  push_neg at hno
  have hno' : ∀ p, ∃ ε > 0, ∀ τ, sInf (triggerTimes input s) ≤ τ →
      τ < sInf (triggerTimes input s) + ε → ¬ TriggerCond input s.x s.pending s.claims τ p := by
    intro p
    have := hno p
    unfold Critical at this
    push_neg at this
    exact this
  choose ε hε hε' using hno'
  obtain ⟨t0, -, p0, -⟩ := id hne
  set δ := Finset.univ.inf' ⟨p0, Finset.mem_univ p0⟩ ε with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun p _ => hε p
  obtain ⟨t, htT, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (triggerTimes input s)) hδ)
  obtain ⟨p, hp⟩ := htT.2
  have hle : δ ≤ ε p := Finset.inf'_le ε (Finset.mem_univ p)
  exact hε' p t (csInf_le hbdd htT) (by linarith) hp

/-- After an advance, some page is critical. -/
theorem triggerPage_advance (hv : input.Valid) (s : Snap Page)
    (hs : ∀ ρ ∈ s.pending, ρ ∈ input.requests) (hne : (triggerTimes input s).Nonempty) :
    triggerPage input { s with now := sInf (triggerTimes input s) } ≠ none := by
  obtain ⟨p, hp⟩ := exists_critical_sInf input hne
  unfold triggerPage
  rw [Ne, List.find?_eq_none]
  push_neg
  exact ⟨p, by simp [pageOrder], by simpa using hp⟩

theorem triggerPage_nil (hv : input.Valid) {s : Snap Page} (hc : ∀ q, 0 ≤ s.claims q)
    (h : s.pending = []) : triggerPage input s = none := by
  unfold triggerPage
  rw [List.find?_eq_none]
  intro q _
  rw [h]
  simpa using not_critical_nil input hv hc

theorem triggerTimes_nil (hv : input.Valid) {s : Snap Page} (hc : ∀ q, 0 ≤ s.claims q)
    (h : s.pending = []) : triggerTimes input s = ∅ := by
  ext τ
  simp only [triggerTimes, h, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_exists]
  intro _ q
  exact not_triggerCond_nil input hv hc

theorem now_le_sInf (s : Snap Page) (hne : (triggerTimes input s).Nonempty) :
    s.now ≤ sInf (triggerTimes input s) :=
  le_csInf hne fun _ h => h.1

end Trigger

/-! ### Claims stay nonnegative -/

theorem update_zero_nonneg {f : Page → ℝ} (hf : ∀ q, 0 ≤ f q) (a : Page) :
    ∀ q, 0 ≤ Function.update f a 0 q := by
  intro q
  rw [Function.update_apply]
  split_ifs
  exacts [le_rfl, hf q]

theorem claimUpdate_nonneg (input : Instance Page) (hv : input.Valid) (x : Page → ℝ)
    (L : List (Request Page)) {c : Page → ℝ} (hc : ∀ q, 0 ≤ c q) (τ : ℝ) (p : Page) :
    ∀ q, 0 ≤ claimUpdate input x L c τ p q := by
  intro q
  unfold claimUpdate
  split_ifs
  · have hθ : 0 ≤ claimFraction input x L c τ p :=
      le_min zero_le_one (div_nonneg (div_nonneg (Real.sInf_nonneg fun _ h => h.1)
        (Instance.L_pos hv).le) (Finset.sum_nonneg fun q _ => le_max_left _ _))
    have ho : 0 ≤ overshoot input L c q τ := le_max_left _ _
    nlinarith [hc q]
  · exact hc q

/-! ### Invariants of a single run -/

section Single

variable (input : Instance Page)

/-- The run invariant: times are sorted from `now` on, upcoming times are distinct, pending requests are requests of the instance, claims are nonnegative. -/
structure Inv (s : Snap Page) : Prop where
  sorted : (s.now :: s.upcoming).Pairwise (· ≤ ·)
  nodup : s.upcoming.Nodup
  pending : ∀ ρ ∈ s.pending, ρ ∈ input.requests
  claims : ∀ q, 0 ≤ s.claims q

/-- The weight of one unit of `load`. -/
def K : ℕ := 2 * numLevels input + 4

/-- A rank of the state, decreasing along the level loop; in the idle stage it is `0` iff some page triggers now. -/
def rank (s : Snap Page) : ℕ :=
  match s.stage with
  | .idle => if triggerPage input s = none then 1 else 0
  | .examine e => 2 * (maxLevel input - e).toNat + 3
  | .preempt e _ => 2 * (maxLevel input - e).toNat + 2

/-- Arrival times still to come, requests still to arrive, pending requests. -/
def load (s : Snap Page) : ℕ :=
  s.upcoming.length + (input.requests.filter fun ρ => decide (ρ.arrival ∈ s.upcoming)).length +
    s.pending.length

/-- The termination measure. -/
def meas (s : Snap Page) : ℕ := load input s * K input + rank input s

theorem rank_idle {s : Snap Page} (h : s.stage = .idle) :
    rank input s = if triggerPage input s = none then 1 else 0 := by
  unfold rank; rw [h]

theorem rank_examine {s : Snap Page} {e : ℤ} (h : s.stage = .examine e) :
    rank input s = 2 * (maxLevel input - e).toNat + 3 := by
  unfold rank; rw [h]

theorem rank_preempt {s : Snap Page} {e : ℤ} {b : Page → ℝ} (h : s.stage = .preempt e b) :
    rank input s = 2 * (maxLevel input - e).toNat + 2 := by
  unfold rank; rw [h]

theorem rank_idle_le {s : Snap Page} (h : s.stage = .idle) : rank input s ≤ 1 := by
  rw [rank_idle input h]; split_ifs <;> omega

theorem rank_afterLevel {s : Snap Page} {e : ℤ} (h : s.stage = afterLevel input e) :
    rank input s < 2 * (maxLevel input - e).toNat + 2 := by
  unfold afterLevel at h
  split_ifs at h with he
  · rw [rank_examine input h]; omega
  · have := rank_idle_le input h; omega

theorem rank_minLevel_lt {s : Snap Page} (h : s.stage = .examine (minLevel input)) :
    rank input s < K input := by
  rw [rank_examine input h]
  unfold K numLevels
  omega

theorem count_split (R : List (Request Page)) (t : ℝ) (rest : List ℝ) (ht : t ∉ rest) :
    (R.filter fun ρ => decide (ρ.arrival ∈ t :: rest)).length =
      (R.filter fun ρ => decide (ρ.arrival = t)).length +
        (R.filter fun ρ => decide (ρ.arrival ∈ rest)).length := by
  induction R with
  | nil => simp
  | cons ρ R ih =>
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> (try simp only [List.length_cons]) <;>
      first | omega | (exfalso; simp only [decide_eq_true_eq, List.mem_cons] at *; grind)

theorem next_step (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (hn : next input s = some (m, s')) :
    Inv input s' ∧ s.now ≤ s'.now ∧ (∀ w ∈ waypoints input s m, s.now ≤ w.time ∧ w.time ≤ s'.now) ∧
      meas input s' < meas input s := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  have K4 : 4 ≤ K input := by unfold K; omega
  cases hst : s.stage with
  | idle =>
    cases htp : triggerPage input s with
    | some q =>
      rw [next_critical input hst htp] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      obtain ⟨ρ, hρ, hρq⟩ := exists_pending_of_critical input hv hs4 (critical_of_triggerPage input htp)
      have hlt : (s.pending.filter fun π => decide (π.page ≠ q)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨ρ, hρ, by simp [hρq]⟩
      refine ⟨⟨hs1, hs2, fun π h => hs3 π (List.mem_filter.mp h).1,
        update_zero_nonneg (claimUpdate_nonneg input hv _ _ hs4 _ _) _⟩, le_rfl, ?_, ?_⟩
      · simp [waypoints]
      · have hr := rank_minLevel_lt input (s := { s with
          x := criticalState input s.x q
          budget := deposit input s.x q s.budget
          pending := s.pending.filter fun π => decide (π.page ≠ q)
          claims := Function.update (claimUpdate input s.x s.pending s.claims s.now q) q 0
          stage := .examine (minLevel input) }) rfl
        have h0 : rank input s = 0 := by rw [rank_idle input hst, htp]; simp
        unfold meas load
        try dsimp only at hr ⊢
        rw [h0]
        nlinarith
    | none =>
      have h1 : rank input s = 1 := by rw [rank_idle input hst, htp]; simp
      by_cases hc : (triggerTimes input s).Nonempty ∧
          ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a
      · rw [next_advance input hst htp hc] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        have hle := now_le_sInf input s hc.1
        refine ⟨⟨?_, hs2, hs3, hs4⟩, hle, by simp [waypoints, hle], ?_⟩
        · dsimp only
          refine List.Pairwise.cons ?_ (List.Pairwise.of_cons hs1)
          intro b hb
          cases hup : s.upcoming with
          | nil => rw [hup] at hb; simp at hb
          | cons a r =>
            rw [hup] at hb hs1
            have ha := hc.2 a (by simp [hup])
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ha.le
            · exact ha.le.trans ((List.pairwise_cons.mp (List.Pairwise.of_cons hs1)).1 b hb)
        · have h0 : rank input { s with now := sInf (triggerTimes input s) } = 0 := by
            rw [rank_idle input (s := { s with now := sInf (triggerTimes input s) }) hst]
            simp [triggerPage_advance input hv s hs3 hc.1]
          unfold meas load
          try dsimp only
          rw [h0, h1]
          omega
      · cases hup : s.upcoming with
        | nil => rw [next_none input hst htp hc hup] at hn; cases hn
        | cons a r =>
          rw [next_tick input hst htp hc hup] at hn
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
          rw [hup] at hs1 hs2
          have ha : a ∉ r := (List.nodup_cons.mp hs2).1
          have hnowa : s.now ≤ a := (List.pairwise_cons.mp hs1).1 a (by simp)
          refine ⟨⟨(List.pairwise_cons.mp hs1).2, (List.nodup_cons.mp hs2).2, ?_, hs4⟩,
            hnowa, ?_, ?_⟩
          · intro π hπ
            rcases List.mem_append.mp (List.mem_filter.mp hπ).1 with h | h
            · exact hs3 π h
            · exact (List.mem_filter.mp h).1
          · simp only [waypoints, List.mem_singleton]
            rintro w rfl
            exact ⟨hnowa, le_rfl⟩
          · have hr := rank_idle_le input (s := { s with
              now := a
              upcoming := r
              pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a)).filter
                fun ρ => decide (s.x ρ.page ≠ input.delta) }) hst
            unfold meas load
            try dsimp only at hr ⊢
            rw [hup, h1, count_split _ _ _ ha]
            have := List.length_filter_le (fun ρ => decide (s.x ρ.page ≠ input.delta))
              (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a))
            rw [List.length_append] at this
            simp only [List.length_cons]
            nlinarith
  | examine e =>
    by_cases hpc : preemptCondition input s.x s.budget e
    · rw [next_openHole input hst hpc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, by simp [waypoints], ?_⟩
      unfold meas load
      try dsimp only
      rw [rank_examine input hst, rank_preempt input (s := { s with
        x := hole input s.x e
        budget := Function.update s.budget e (s.budget e - holePayment input e)
        stage := .preempt e s.x }) rfl]
      omega
    · rw [next_skip input hst hpc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, by simp [waypoints], ?_⟩
      have := rank_afterLevel input (s := { s with stage := afterLevel input e }) rfl
      unfold meas load
      try dsimp only at this ⊢
      rw [rank_examine input hst]
      omega
  | preempt e b =>
    cases htc : tripCandidate input s.pending s.now e with
    | none =>
      rw [next_closeNone input hst htc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, ?_, ?_⟩
      · simp [waypoints, hst]
      · have := rank_afterLevel input (s := { s with x := b, stage := afterLevel input e }) rfl
        unfold meas load
        try dsimp only at this ⊢
        rw [rank_preempt input hst]
        omega
    | some π =>
      have hmem : π ∈ s.pending := (List.mem_filter.mp (List.argmin_mem htc)).1
      by_cases hcost : levelWeight e ≤ s.budget e
      · rw [next_trip input hst htc hcost] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        have hlt : (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length <
            s.pending.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨π, hmem, by simp⟩
        refine ⟨⟨hs1, hs2, fun ρ h => hs3 ρ (List.mem_filter.mp h).1,
          update_zero_nonneg hs4 _⟩, le_rfl, ?_, ?_⟩
        · simp [waypoints]
        · unfold meas load
          try dsimp only
          rw [rank_preempt input hst, rank_preempt input (s := { s with
            budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
            pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
            claims := Function.update s.claims π.page 0 }) hst]
          nlinarith
      · rw [next_closeSome input hst htc hcost] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, ?_, ?_⟩
        · simp [waypoints, hst]
        · have := rank_afterLevel input (s := { s with x := b, stage := afterLevel input e }) rfl
          unfold meas load
          try dsimp only at this ⊢
          rw [rank_preempt input hst]
          omega

theorem run_indep (hv : input.Valid) : ∀ (n m : ℕ) (s : Snap Page), Inv input s → meas input s < n →
    meas input s < m → run input n s = run input m s := by
  intro n
  induction n with
  | zero => intro m s _ h; omega
  | succ n ih =>
    intro m s hs hn hm
    cases m with
    | zero => omega
    | succ m =>
      simp only [run]
      cases hnx : next input s with
      | none => rfl
      | some pr =>
        obtain ⟨mv, s'⟩ := pr
        obtain ⟨hi, -, -, hme⟩ := next_step input hv hs hnx
        try dsimp only
        rw [ih m s' hi (by omega) (by omega)]

/-- The waypoints of a log up to time `t`. -/
def F (t : ℝ) (L : List (Entry Page)) : List (Waypoint Page) :=
  (L.flatMap fun e => waypoints input e.1 e.2).filter fun w => decide (w.time ≤ t)

theorem F_nil (t : ℝ) : F input t ([] : List (Entry Page)) = [] := by simp [F]

theorem F_cons (t : ℝ) (e : Entry Page) (L : List (Entry Page)) :
    F input t (e :: L) = (waypoints input e.1 e.2).filter (fun w => decide (w.time ≤ t)) ++ F input t L := by
  simp [F, List.filter_append]

theorem later (hv : input.Valid) (t : ℝ) :
    ∀ (n : ℕ) (s : Snap Page), Inv input s → t < s.now → F input t (run input n s).1 = [] := by
  intro n
  induction n with
  | zero => intro s _ _; simp [run, F_nil]
  | succ n ih =>
    intro s hs ht
    simp only [run]
    cases hnx : next input s with
    | none => simp [F_nil]
    | some pr =>
      obtain ⟨mv, s'⟩ := pr
      obtain ⟨hi, hle, hw, -⟩ := next_step input hv hs hnx
      try dsimp only
      rw [F_cons, ih s' hi (lt_of_lt_of_le ht hle), List.append_nil, List.filter_eq_nil_iff]
      intro w hmem
      have := (hw w hmem).1
      simp only [decide_eq_true_eq, not_le]
      linarith

/-- The run stops, or its next move records only waypoints after `t` and moves `now` past `t`. -/
def Stop (t : ℝ) (s : Snap Page) : Prop :=
  next input s = none ∨
    ∃ m s', next input s = some (m, s') ∧ t < s'.now ∧ ∀ w ∈ waypoints input s m, t < w.time

theorem stop_nil (hv : input.Valid) (t : ℝ) {s : Snap Page} (hs : Inv input s) (h : Stop input t s)
    (n : ℕ) : F input t (run input n s).1 = [] := by
  cases n with
  | zero => simp [run, F_nil]
  | succ n =>
    rcases h with h | ⟨m, s', h, ht, hw⟩
    · simp [run, h, F_nil]
    · simp only [run, h]
      obtain ⟨hi, -, -, -⟩ := next_step input hv hs h
      rw [F_cons, later input hv t n s' hi ht, List.append_nil, List.filter_eq_nil_iff]
      intro w hwm
      simpa using hw w hwm

/-- In the idle stage with no page triggering now, if neither a trigger time nor an arrival time `≤ t` is ahead, the next move happens after `t`. -/
theorem stop_idle (t : ℝ) {s : Snap Page} (hst : s.stage = .idle)
    (htp : triggerPage input s = none) (hup : ∀ a ∈ s.upcoming.head?, t < a)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧ sInf (triggerTimes input s) ≤ t)) : Stop input t s := by
  by_cases hc' : (triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a
  · right
    have hlt : t < sInf (triggerTimes input s) := by
      by_contra h
      exact hc ⟨hc'.1, not_lt.mp h⟩
    exact ⟨_, _, next_advance input hst htp hc', hlt, by simp [waypoints, hlt]⟩
  · cases hu : s.upcoming with
    | nil => left; exact next_none input hst htp hc' hu
    | cons a r =>
      right
      have ha : t < a := hup a (by simp [hu])
      refine ⟨_, _, next_tick input hst htp hc' hu, ha, ?_⟩
      simp [waypoints, ha]

theorem inv_initial : Inv input (initialSnap input) := by
  have hp : (arrivalTimes input).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hn : (arrivalTimes input).Nodup := Finset.sort_nodup _ _
  refine ⟨?_, hn, by simp [initialSnap], fun _ => le_rfl⟩
  unfold initialSnap
  try dsimp only
  generalize arrivalTimes input = l at *
  cases l with
  | nil => simp
  | cons a l =>
    refine List.Pairwise.cons ?_ hp
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_rfl
    · exact (List.pairwise_cons.mp hp).1 b hb

theorem length_arrivalTimes : (arrivalTimes input).length ≤ input.requests.length := by
  unfold arrivalTimes
  rw [Finset.length_sort]
  exact (List.toFinset_card_le _).trans (by simp)

/-- The only property of `fuel` used: it is at least `(2 |requests| + 1) · K`. -/
theorem fuel_ge : (2 * input.requests.length + 1) * K input ≤ fuel input := by
  unfold fuel K
  have := Nat.mul_le_mul_right (2 * numLevels input + 4)
    (show 2 * input.requests.length + 1 ≤ 4 * input.requests.length + 1 by omega)
  omega

theorem meas_initial : meas input (initialSnap input) < fuel input := by
  have hl : load input (initialSnap input) ≤ 2 * input.requests.length := by
    have h1 := length_arrivalTimes input
    have h2 := List.length_filter_le
      (fun ρ : Request Page => decide (ρ.arrival ∈ arrivalTimes input)) input.requests
    unfold load initialSnap
    try dsimp only
    simp only [List.length_nil, add_zero]
    omega
  have hr : rank input (initialSnap input) ≤ 1 := rank_idle_le input rfl
  have hf := fuel_ge input
  have K4 : 4 ≤ K input := by unfold K; omega
  have := Nat.mul_le_mul_right (K input) hl
  unfold meas
  nlinarith

end Single

/-! ### Two runs -/

/-- Related snapshots of the runs on two instances that agree up to time `t`. -/
structure Rel (I1 I2 : Instance Page) (t : ℝ) (s1 s2 : Snap Page) : Prop where
  x : s1.x = s2.x
  budget : s1.budget = s2.budget
  pending : s1.pending = s2.pending
  claims : s1.claims = s2.claims
  stage : s1.stage = s2.stage
  up : s1.upcoming.filter (fun a => decide (a ≤ t)) = s2.upcoming.filter (fun a => decide (a ≤ t))
  inv1 : Inv I1 s1
  inv2 : Inv I2 s2
  now : (s1.now = s2.now ∧ s1.now ≤ t) ∨ (s1.pending = [] ∧ s1.stage = .idle)

variable (t : ℝ)

theorem step_sim (hv1 : I1.Valid) (hv2 : I2.Valid) (hS : Same I1 I2)
    (hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a))
    {s1 s2 : Snap Page} (hR : Rel I1 I2 t s1 s2) :
    (Stop I1 t s1 ∧ Stop I2 t s2) ∨
      ∃ m s1' s2', next I1 s1 = some (m, s1') ∧ next I2 s2 = some (m, s2') ∧
        waypoints I1 s1 m = waypoints I2 s2 m ∧ Rel I1 I2 t s1' s2' := by
  obtain ⟨hx, hb, hp, hc, hst, hup, hi1, hi2, hnow⟩ := hR
  cases hst1 : s1.stage with
  | idle =>
    have hst2 : s2.stage = .idle := hst ▸ hst1
    have hsame : (s1.now = s2.now ∧ s1.now ≤ t) ∨ (s1.pending = [] ∧ s2.pending = []) := by
      rcases hnow with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hp ▸ h⟩
    have htp : triggerPage I2 s2 = triggerPage I1 s1 := by
      rcases hsame with ⟨hn, -⟩ | ⟨h1, h2⟩
      · rw [← hS.triggerPage]; simp only [triggerPage, hx, hp, hc, hn]
      · rw [triggerPage_nil I1 hv1 hi1.claims h1, triggerPage_nil I2 hv2 hi2.claims h2]
    have htt : triggerTimes I2 s2 = triggerTimes I1 s1 := by
      rcases hsame with ⟨hn, -⟩ | ⟨h1, h2⟩
      · rw [← hS.triggerTimes]; simp only [triggerTimes, hx, hp, hc, hn]
      · rw [triggerTimes_nil I1 hv1 hi1.claims h1, triggerTimes_nil I2 hv2 hi2.claims h2]
    cases htp1 : triggerPage I1 s1 with
    | some q =>
      have hn : s1.now = s2.now ∧ s1.now ≤ t := by
        rcases hsame with h | ⟨h1, -⟩
        · exact h
        · rw [triggerPage_nil I1 hv1 hi1.claims h1] at htp1; cases htp1
      right
      have e1 := next_critical I1 hst1 htp1
      have e2 := next_critical I2 hst2 (htp.trans htp1)
      refine ⟨_, _, _, e1, e2, ?_, ⟨?_, ?_, ?_, ?_, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hS.criticalState, hx, hn.1]
      · (try dsimp only); rw [hS.criticalState, hx]
      · (try dsimp only); rw [hS.deposit, hx, hb]
      · (try dsimp only); rw [hp]
      · (try dsimp only); rw [hS.claimUpdate, hx, hp, hc, hn.1]
      · (try dsimp only); rw [hS.minLevel]
    | none =>
      have htp2 : triggerPage I2 s2 = none := htp.trans htp1
      rcases PagingWithDelay.PMD.OnlineProof.heads t (List.Pairwise.of_cons hi1.sorted)
          (List.Pairwise.of_cons hi2.sorted) hup with
        ⟨h1, h2⟩ | ⟨a, r1, r2, ha, hu1, hu2, hr⟩
      · by_cases hT : (triggerTimes I1 s1).Nonempty ∧ sInf (triggerTimes I1 s1) ≤ t
        · right
          have c1 : (triggerTimes I1 s1).Nonempty ∧
              ∀ a ∈ s1.upcoming.head?, sInf (triggerTimes I1 s1) < a :=
            ⟨hT.1, fun a h => lt_of_le_of_lt hT.2 (h1 a h)⟩
          have c2 : (triggerTimes I2 s2).Nonempty ∧
              ∀ a ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < a := by
            rw [htt]; exact ⟨hT.1, fun a h => lt_of_le_of_lt hT.2 (h2 a h)⟩
          have e1 := next_advance I1 hst1 htp1 c1
          have e2 := next_advance I2 hst2 htp2 c2
          have i2 := (next_step I2 hv2 hi2 e2).1
          rw [htt] at e2 i2
          refine ⟨_, _, _, e1, e2, by simp only [waypoints, hx], ⟨hx, hb, hp, hc, hst, hup,
            (next_step I1 hv1 hi1 e1).1, i2, Or.inl ⟨rfl, hT.2⟩⟩⟩
        · left
          exact ⟨stop_idle I1 t hst1 htp1 h1 hT, stop_idle I2 t hst2 htp2 h2 (htt ▸ hT)⟩
      · right
        by_cases hT : (triggerTimes I1 s1).Nonempty ∧
            ∀ b ∈ s1.upcoming.head?, sInf (triggerTimes I1 s1) < b
        · have c2 : (triggerTimes I2 s2).Nonempty ∧
              ∀ b ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < b := by
            rw [htt, hu2]; rw [hu1] at hT; exact hT
          have hlt : sInf (triggerTimes I1 s1) < a := hT.2 a (by simp [hu1])
          have e1 := next_advance I1 hst1 htp1 hT
          have e2 := next_advance I2 hst2 htp2 c2
          have i2 := (next_step I2 hv2 hi2 e2).1
          rw [htt] at e2 i2
          refine ⟨_, _, _, e1, e2, by simp only [waypoints, hx], ⟨hx, hb, hp, hc, hst, hup,
            (next_step I1 hv1 hi1 e1).1, i2, Or.inl ⟨rfl, hlt.le.trans ha⟩⟩⟩
        · have c2 : ¬ ((triggerTimes I2 s2).Nonempty ∧
              ∀ b ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < b) := by
            rw [htt, hu2]; rw [hu1] at hT; exact hT
          have e1 := next_tick I1 hst1 htp1 hT hu1
          have e2 := next_tick I2 hst2 htp2 c2 hu2
          refine ⟨_, _, _, e1, e2, ?_, ⟨hx, hb, ?_, hc, hst, hr,
            (next_step I1 hv1 hi1 e1).1, (next_step I2 hv2 hi2 e2).1, Or.inl ⟨rfl, ha⟩⟩⟩
          · simp only [waypoints, hx]
          · (try dsimp only); rw [hp, hreq a ha, hx, hS.delta]
  | examine e =>
    have hst2 : s2.stage = .examine e := hst ▸ hst1
    have hn : s1.now = s2.now ∧ s1.now ≤ t := by
      rcases hnow with h | ⟨-, h⟩
      · exact h
      · rw [hst1] at h; cases h
    right
    by_cases hpc : preemptCondition I1 s1.x s1.budget e
    · have hpc2 : preemptCondition I2 s2.x s2.budget e := by
        rw [← hS.preemptCondition, ← hx, ← hb]; exact hpc
      have e1 := next_openHole I1 hst1 hpc
      have e2 := next_openHole I2 hst2 hpc2
      refine ⟨_, _, _, e1, e2, ?_, ⟨?_, ?_, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hS.hole, hx, hn.1]
      · (try dsimp only); rw [hS.hole, hx]
      · (try dsimp only); rw [hS.holePayment, hb]
      · (try dsimp only); rw [hx]
    · have hpc2 : ¬ preemptCondition I2 s2.x s2.budget e := by
        rw [← hS.preemptCondition, ← hx, ← hb]; exact hpc
      have e1 := next_skip I1 hst1 hpc
      have e2 := next_skip I2 hst2 hpc2
      refine ⟨_, _, _, e1, e2, rfl, ⟨hx, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      (try dsimp only); rw [hS.afterLevel]
  | preempt e b =>
    have hst2 : s2.stage = .preempt e b := hst ▸ hst1
    have hn : s1.now = s2.now ∧ s1.now ≤ t := by
      rcases hnow with h | ⟨-, h⟩
      · exact h
      · rw [hst1] at h; cases h
    right
    have htc : tripCandidate I2 s2.pending s2.now e = tripCandidate I1 s1.pending s1.now e := by
      rw [← hS.tripCandidate, hp, hn.1]
    cases htc1 : tripCandidate I1 s1.pending s1.now e with
    | none =>
      have e1 := next_closeNone I1 hst1 htc1
      have e2 := next_closeNone I2 hst2 (htc.trans htc1)
      refine ⟨_, _, _, e1, e2, ?_, ⟨rfl, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hst1, hst2, hn.1]
      · (try dsimp only); rw [hS.afterLevel]
    | some π =>
      by_cases hcost : levelWeight e ≤ s1.budget e
      · have hcost2 : levelWeight e ≤ s2.budget e := by
          rw [← hb]; exact hcost
        have e1 := next_trip I1 hst1 htc1 hcost
        have e2 := next_trip I2 hst2 (htc.trans htc1) hcost2
        refine ⟨_, _, _, e1, e2, ?_, ⟨hx, ?_, ?_, ?_, hst, hup, (next_step I1 hv1 hi1 e1).1,
          (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
        · simp only [waypoints, hS.delta, hx, hn.1]
        · (try dsimp only); rw [hS.tripCost, hx, hb]
        · (try dsimp only); rw [hp]
        · (try dsimp only); rw [hc]
      · have hcost2 : ¬ levelWeight e ≤ s2.budget e := by
          rw [← hb]; exact hcost
        have e1 := next_closeSome I1 hst1 htc1 hcost
        have e2 := next_closeSome I2 hst2 (htc.trans htc1) hcost2
        refine ⟨_, _, _, e1, e2, ?_, ⟨rfl, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
          (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
        · simp only [waypoints, hst1, hst2, hn.1]
        · (try dsimp only); rw [hS.afterLevel]

theorem sim (hv1 : I1.Valid) (hv2 : I2.Valid) (hS : Same I1 I2)
    (hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a)) :
    ∀ (n : ℕ) (s1 s2 : Snap Page), Rel I1 I2 t s1 s2 →
      F I1 t (run I1 n s1).1 = F I2 t (run I2 n s2).1 := by
  intro n
  induction n with
  | zero => intro s1 s2 _; simp [run, F_nil]
  | succ n ih =>
    intro s1 s2 hR
    rcases step_sim t hv1 hv2 hS hreq hR with ⟨h1, h2⟩ | ⟨m, s1', s2', e1, e2, hw, hR'⟩
    · rw [stop_nil I1 hv1 t hR.inv1 h1, stop_nil I2 hv2 t hR.inv2 h2]
    · simp only [run, e1, e2]
      rw [F_cons, F_cons, ih s1' s2' hR']
      simp only [hw]

theorem mem_arrivalTimes (input : Instance Page) {a : ℝ} (ha : a ≤ t) :
    a ∈ arrivalTimes input ↔
      ∃ ρ ∈ input.requests.filter (fun ρ => decide (ρ.arrival ≤ t)), ρ.arrival = a := by
  simp only [arrivalTimes, Finset.mem_sort, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, ⟨hρ, ha⟩, rfl⟩
  · rintro ⟨ρ, ⟨hρ, -⟩, h⟩
    exact ⟨ρ, hρ, h⟩

theorem arrivalTimes_filter
    (hf : (I1.requests.filter fun ρ => decide (ρ.arrival ≤ t)) =
      I2.requests.filter fun ρ => decide (ρ.arrival ≤ t)) :
    (arrivalTimes I1).filter (fun a => decide (a ≤ t)) =
      (arrivalTimes I2).filter (fun a => decide (a ≤ t)) := by
  have p1 : (arrivalTimes I1).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have p2 : (arrivalTimes I2).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have n1 : (arrivalTimes I1).Nodup := Finset.sort_nodup _ _
  have n2 : (arrivalTimes I2).Nodup := Finset.sort_nodup _ _
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (p1.filter _) (p2.filter _)
  · rw [List.perm_ext_iff_of_nodup (n1.filter _) (n2.filter _)]
    intro a
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨(mem_arrivalTimes t I2 ha).mpr (hf ▸ (mem_arrivalTimes t I1 ha).mp h), ha⟩
    · rintro ⟨h, ha⟩
      exact ⟨(mem_arrivalTimes t I1 ha).mpr (hf ▸ (mem_arrivalTimes t I2 ha).mp h), ha⟩

end OnlineProof

end

open OnlineProof in
/-- **`PMD` is online**: the waypoints up to time `t` depend only on the requests that have arrived by `t`. -/
theorem preemptiveMirrorDescent_online : (preemptiveMirrorDescent : FracAlgorithm Page).Online := by
  intro I1 I2 t h
  have hv1 := I1.valid
  have hv2 := I2.valid
  have hw : (I1.upTo t).weight = (I2.upTo t).weight := congrArg _ h
  have hk : (I1.upTo t).cacheSize = (I2.upTo t).cacheSize := congrArg _ h
  have hC : (I1.upTo t).initialCache = (I2.upTo t).initialCache := congrArg _ h
  have hi₀ : (I1.upTo t).startPage = (I2.upTo t).startPage := congrArg _ h
  have hπ : (I1.upTo t).tieRank = (I2.upTo t).tieRank := congrArg _ h
  have hS : Same I1 I2 := ⟨hw, hk, hC, hi₀, hπ⟩
  have hf : (I1.requests.filter fun ρ => decide (ρ.arrival ≤ t)) =
      I2.requests.filter fun ρ => decide (ρ.arrival ≤ t) := congrArg Instance.requests h
  have hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a) := by
    intro a ha
    have key : ∀ R : List (Request Page), (R.filter fun ρ => decide (ρ.arrival = a)) =
        (R.filter fun ρ => decide (ρ.arrival ≤ t)).filter fun ρ => decide (ρ.arrival = a) := by
      intro R
      rw [List.filter_filter]
      congr 1
      funext ρ
      by_cases hρ : ρ.arrival = a
      · simp [hρ, ha]
      · simp [hρ]
    rw [key, hf, ← key]
  have hR : Rel I1 I2 t (initialSnap I1) (initialSnap I2) :=
    ⟨by show initialState I1 = initialState I2; rw [hS.initialState], rfl, rfl, rfl, rfl,
      arrivalTimes_filter t hf, inv_initial I1, inv_initial I2, Or.inr ⟨rfl, rfl⟩⟩
  have e1 := run_indep I1 hv1 (fuel I1) (max (fuel I1) (fuel I2)) (initialSnap I1)
    (inv_initial I1) (meas_initial I1) (lt_of_lt_of_le (meas_initial I1) (le_max_left _ _))
  have e2 := run_indep I2 hv2 (fuel I2) (max (fuel I1) (fuel I2)) (initialSnap I2)
    (inv_initial I2) (meas_initial I2) (lt_of_lt_of_le (meas_initial I2) (le_max_right _ _))
  have := sim t hv1 hv2 hS hreq (max (fuel I1) (fuel I2)) _ _ hR
  simp only [F] at this
  simp only [preemptiveMirrorDescent, FracSchedule.upTo, log, e1, e2]
  exact this

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

theorem mem_pageOrder (p : Page) : p ∈ pageOrder input := by
  simp [pageOrder]

theorem pageOrder_pairwise :
    (pageOrder input).Pairwise fun a b => input.tieRank a ≤ input.tieRank b := by
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (input.tieRank a ≤ input.tieRank b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (Finset.univ : Finset Page).toList
  simpa [pageOrder] using h

/-- **Tie-break of the trigger page**: it has the least `tieRank` among the pages critical now. -/
theorem triggerPage_tieRank_le {s : Snap Page} {p : Page} (h : triggerPage input s = some p)
    {q : Page} (hq : Critical input s.x s.pending s.claims s.now q) :
    input.tieRank p ≤ input.tieRank q := by
  unfold triggerPage at h
  obtain ⟨-, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.1 h
  have hpw := pageOrder_pairwise (input := input)
  have hqm := mem_pageOrder (input := input) q
  rw [hl] at hpw hqm
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  rcases List.mem_append.1 hqm with hqa | hqb
  · have := has q hqa
    simp [hq] at this
  · rcases List.mem_cons.1 hqb with rfl | hqb
    · exact le_rfl
    · exact hpw.2.1.1 q hqb

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
    exact h p (mem_pageOrder p) (by simpa using hp)
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

/-! ## Inlined from `PagingWithDelay.Analysis.Cost` -/
section

/-!
# The fetch cost of `PMD` (`prop:preemptfetch`, `lem:lengthfetch`)

The fetch cost of `PMD`, in terms of the critical services of the log.

* A critical service `λ` deposits `|λ|_W` into `B_W` for `w_p ≤ W ≤ w_max`, in total at most `|λ|` (`sum_levelLen_le`); the budgets start at `0` and stay nonnegative, so the payments for holes and round trips are at most `∑_λ |λ|` (`holeTotal_add_tripTotal_le`).
* `|λ| ≤ 3 EV(λ)` (`lem:clock`), so `∑_λ |λ| ≤ 3 ∑_λ EV(λ)` (`lenTotal_le`).
* `∑_λ EV(λ) ≤ ∑_λ fetch(λ) + ∑ wᵢ` (`lem:evfetch`), by telescoping `∑ᵢ wᵢ xᵢ` of the base state (`evTotal_le`); with the previous item this is `lem:lengthfetch` (`lenTotal_le_fetchTotal`).
* A critical service fetches `fetch(λ)`, a round trip its cost, closing a hole at most its payment `W (1 - δ)`; nothing else fetches (`fetchCost_le_preempt`; with the budget bound this is `prop:preemptfetch`, `fetchCost_le_lenTotal`).

Hence the fetch cost is at most `4 ∑_λ fetch(λ) + 3 ∑ wᵢ` (`fetchCost_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PagingWithDelay

namespace PMD

namespace CostProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch criticalEV hole holePayment preemptCondition tripCost afterLevel Stage IsRest
  IsFrac pathFrom lastState dFetch closingCost pathFrom_cons pathFrom_nil dFetch_self)

noncomputable section

variable (input : Instance Page)

/-! ### Helpers: per-entry contributions -/

/-- The closing cost of the hole opened by entry `i`, if it opens one. -/
def openAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .openHole e => closingCost input (snapAt input i).x e
    | _ => 0
  else 0

/-- The closing cost of the currently open hole (`0` outside a preemptive service). -/
def pendingClose (s : Snap Page) : ℝ :=
  match s.stage with
  | .preempt e b => closingCost input b e
  | _ => 0

/-- The closing cost of the hole closed by entry `i`, if it closes one. -/
def closeAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .closeHole _ _ => pendingClose input (snapAt input i)
    | _ => 0
  else 0

open scoped InstanceNotation in
/-- The weighted mass `∑ⱼ wⱼ xⱼ` of the base state. -/
def baseMass (s : Snap Page) : ℝ := ∑ j, w j * baseState s j

/-- The total budget of all levels. -/
def totalBudget (s : Snap Page) : ℝ :=
  ∑ e ∈ Finset.Icc (minLevel input) (maxLevel input), s.budget e

variable {input}

theorem pendingClose_afterLevel (s : Snap Page) (e : ℤ) :
    pendingClose input { s with stage := afterLevel input e } = 0 := by
  unfold pendingClose afterLevel
  split_ifs <;> rfl

theorem sum_update_single (w : Page → ℝ) (x : Page → ℝ) (p : Page) (v : ℝ)
    (g : ℝ → ℝ → ℝ) (hg : ∀ a, g a a = 0) :
    ∑ j, w j * g (Function.update x p v j) (x j) = w p * g v (x p) := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj, hg]
  · simp

section

variable (hv : input.Valid)
include hv

theorem isRest_x_of_not_preempt {i : ℕ}
    (hs : ∀ e b, (snapAt input i).stage ≠ .preempt e b) :
    IsRest input (snapAt input i).x := by
  rw [x_eq_baseState hv hs]; exact baseState_isRest hv i

theorem trip_mem_pending {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) : π ∈ (snapAt input i).pending := by
  obtain ⟨-, hcand, -⟩ := trip_spec hv h hm
  exact (List.mem_filter.1 (List.argmin_mem hcand)).1

open scoped InstanceNotation in
/-- Everything an entry contributes. -/
theorem entry_spec (i : ℕ) (h : i < (log input).length) :
    pathFrom (dFetch input) (snapAt input i).x (wpAt input i) =
      fetchAt input i + tripAt input i + closeAt input i ∧
    pendingClose input (snapAt input (i + 1)) - pendingClose input (snapAt input i) =
      openAt input i - closeAt input i ∧
    totalBudget input (snapAt input (i + 1)) - totalBudget input (snapAt input i) ≤
      lenAt input i - holeAt input i - tripAt input i ∧
    baseMass input (snapAt input (i + 1)) - baseMass input (snapAt input i) =
      evAt input i - fetchAt input i := by
  have hvb := hv
  have hok := stageOK hv i
  have hbase : ∀ (hnp : ∀ p, moveAt i h ≠ .critical p),
      baseMass input (snapAt input (i + 1)) - baseMass input (snapAt input i) = 0 := by
    intro hnp; simp [baseMass, baseState_succ_of_not_critical hv h hnp]
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · -- tick
    have he := (tick_spec hv h hm).2.2.2.2
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil,
      dFetch_self, totalBudget, pendingClose]
    all_goals try first | rfl | ring1 | simp
  · -- advance
    have he := (advance_spec hv h hm).2.2.2.2.2.2
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil,
      dFetch_self, totalBudget, pendingClose]
    all_goals try first | rfl | ring1 | simp
  · -- critical service
    obtain ⟨hs, -, he⟩ := critical_spec hv h hm
    obtain ⟨-, -, hx, hr, -⟩ := critical_facts hv h hm
    have hb0 : baseState (snapAt input i) = (snapAt input i).x := by simp [baseState, hs]
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    rw [he]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [pathFrom_cons, pathFrom_nil, dFetch]
      rw [PagingWithDelay.PMD.critical_fetchCost hvb hx hr]; ring
    · simp [pendingClose, hs]
    · simp only [totalBudget]
      rw [← Finset.sum_sub_distrib]
      have hsum : ∑ e ∈ Finset.Icc (minLevel input) (maxLevel input),
          (deposit input (snapAt input i).x p (snapAt input i).budget e -
            (snapAt input i).budget e) =
          ∑ e ∈ Finset.Icc (level input p) (maxLevel input),
            levelLen input (snapAt input i).x p e := by
        have hsub : Finset.Icc (level input p) (maxLevel input) ⊆
            Finset.Icc (minLevel input) (maxLevel input) :=
          Finset.Icc_subset_Icc (PagingWithDelay.PMD.minLevel_le p) le_rfl
        rw [← Finset.sum_subset hsub]
        · apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_Icc] at he
          simp [deposit, he]
        · intro e _ he
          rw [Finset.mem_Icc] at he
          simp only [deposit]
          rw [if_neg (by tauto)]; ring
      rw [hsum]
      have := sum_levelLen_le (input := input) (snapAt input i).x p
      linarith
    · simp only [baseMass, hb0]
      simp only [baseState]
      have hw := PagingWithDelay.PMD.critical_weightedMass hvb hx hr
      rw [hw]; ring
  · -- skip
    obtain ⟨hs, -, he⟩ := skip_spec hv h hm
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); (try rw [pendingClose_afterLevel]); simp only [pathFrom_nil,
      totalBudget, pendingClose, hs]
    all_goals try first | rfl | ring1 | simp
  · -- openHole
    obtain ⟨hs, -, he⟩ := openHole_spec hv h hm
    have hx : IsRest input (snapAt input i).x :=
      isRest_x_of_not_preempt hv (by rw [hs]; simp)
    have hb := hbase (by rw [hm]; simp)
    rw [hs] at hok
    have hmem : e ∈ Finset.Icc (minLevel input) (maxLevel input) :=
      Finset.mem_Icc.2 hok
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, dFetch,
      pendingClose, hs, totalBudget, PagingWithDelay.PMD.hole_fetch_open hvb hx.1]
    all_goals try first | rfl | ring1 | (rw [sum_update_eq hmem]; linarith)
  · -- trip
    obtain ⟨⟨b, hs⟩, hcand, -, he⟩ := trip_spec hv h hm
    have hπ := trip_mem_pending hv h hm
    have hr : δ < (snapAt input i).x π.page := delta_lt_of_pending hv hπ
    have hb := hbase (by rw [hm]; simp)
    rw [hs] at hok
    have hmem : e ∈ Finset.Icc (minLevel input) (maxLevel input) :=
      Finset.mem_Icc.2 hok
    have h3 : dFetch input (snapAt input i).x
        (Function.update (snapAt input i).x π.page δ) =
        tripCost input (snapAt input i).x π.page := by
      unfold dFetch tripCost
      rw [sum_update_single _ _ _ _ (fun a b => max 0 (b - a)) (by simp)]
      rw [max_eq_right (by simpa using hr.le)]
    have h4 : dFetch input (Function.update (snapAt input i).x π.page δ)
        (snapAt input i).x = 0 := by
      unfold dFetch
      rw [sum_update_single _ _ _ _ (fun a b => max 0 (a - b)) (by simp)]
      rw [max_eq_left (by linarith)]; ring
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, h3, h4,
      pendingClose, hs, totalBudget]
    all_goals try first | rfl | ring1 | (rw [sum_update_eq hmem]; linarith)
  · -- closeHole
    obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    obtain ⟨hx, -⟩ := x_eq_hole hv hs
    have hbr : IsRest input b := by
      have := baseState_isRest hv i; rwa [baseState_of_preempt hs] at this
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints, hs]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, dFetch, hx,
      pendingClose, hs, totalBudget, PagingWithDelay.PMD.hole_fetch_close hvb hbr.1]
    all_goals try first | rfl | ring1 | (unfold afterLevel; split_ifs <;> rfl) | simp

/-! ### Nonnegativity -/

theorem fetchAt_nonneg (i : ℕ) : 0 ≤ fetchAt input i := by
  unfold fetchAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨-, -, -, hr, -⟩ := critical_facts hv h hm
    unfold criticalFetch
    exact mul_nonneg (hv.weight_pos p).le (by linarith)
  · exact le_rfl

theorem lenAt_nonneg (i : ℕ) : 0 ≤ lenAt input i := by
  unfold lenAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    exact C.serviceEnd_nonneg' _ _
  · exact le_rfl

/-- `lem:clock` for every entry: `|λ| ≤ 3 EV(λ)`. -/
theorem lenAt_le (i : ℕ) : lenAt input i ≤ 3 * evAt input i := by
  unfold lenAt evAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨-, -, hx, hr, -⟩ := critical_facts hv h hm
    exact serviceEnd_le_three_mul_criticalEV hv hx hr
  · simp

theorem holeAt_nonneg (i : ℕ) : 0 ≤ holeAt input i := by
  unfold holeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    unfold holePayment
    exact mul_nonneg (PagingWithDelay.PMD.levelWeight_pos e).le
      (by linarith [Instance.delta_lt_one hv])
  · exact le_rfl

open scoped InstanceNotation in
theorem tripAt_nonneg (i : ℕ) : 0 ≤ tripAt input i := by
  unfold tripAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    have hr : δ < (snapAt input i).x π.page :=
      delta_lt_of_pending hv (trip_mem_pending hv h hm)
    unfold tripCost
    exact mul_nonneg (hv.weight_pos _).le (by linarith)
  · exact le_rfl

theorem closeAt_nonneg (i : ℕ) : 0 ≤ closeAt input i := by
  unfold closeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨b, hs, -, -⟩ := closeHole_spec hv h hm
    have hbr : IsRest input b := by
      have := baseState_isRest hv i; rwa [baseState_of_preempt hs] at this
    simp only [pendingClose, hs, PagingWithDelay.PMD.closingCost]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hv.weight_pos j).le
      (by linarith [PagingWithDelay.PMD.le_hole hv hbr.1 e j])
  · exact le_rfl

theorem fetchTotal_nonneg : 0 ≤ fetchTotal input :=
  Finset.sum_nonneg fun i _ => fetchAt_nonneg hv i

theorem lenTotal_nonneg : 0 ≤ lenTotal input :=
  Finset.sum_nonneg fun i _ => lenAt_nonneg hv i

theorem holeTotal_nonneg : 0 ≤ holeTotal input :=
  Finset.sum_nonneg fun i _ => holeAt_nonneg hv i

theorem tripTotal_nonneg : 0 ≤ tripTotal input :=
  Finset.sum_nonneg fun i _ => tripAt_nonneg hv i

/-! ### Payments, deposits and lengths -/

/-- A hole costs at most its payment `W (1 - δ)` to close. -/
theorem openAt_le_holeAt (i : ℕ) : openAt input i ≤ holeAt input i := by
  unfold openAt holeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨hs, -, -⟩ := openHole_spec hv h hm
    have hx : IsRest input (snapAt input i).x :=
      isRest_x_of_not_preempt hv (by rw [hs]; simp)
    have := PagingWithDelay.PMD.closingCost_le hv hx.1 e
    simp only [holePayment]
    linarith
  · exact le_rfl

theorem sum_open_eq_close :
    ∑ i ∈ Finset.range (log input).length, openAt input i =
      ∑ i ∈ Finset.range (log input).length, closeAt input i := by
  have h := Finset.sum_range_sub (fun i => pendingClose input (snapAt input i))
    (log input).length
  rw [Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.1),
    Finset.sum_sub_distrib] at h
  simp only [pendingClose, (final_spec hv).2.2.1, snapAt_zero hv, initialSnap] at h
  linarith

/-- The budget payments (for holes and round trips) are at most the deposits, hence at most the lengths of the critical services. -/
theorem holeTotal_add_tripTotal_le : holeTotal input + tripTotal input ≤ lenTotal input := by
  have h := Finset.sum_range_sub (fun i => totalBudget input (snapAt input i))
    (log input).length
  have hle := Finset.sum_le_sum
    (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.2.1)
  rw [h, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hle
  have hN : 0 ≤ totalBudget input (snapAt input (log input).length) :=
    Finset.sum_nonneg fun e _ => budget_nonneg hv _ e
  have h0 : totalBudget input (snapAt input 0) = 0 := by
    simp [totalBudget, snapAt_zero hv, initialSnap]
  unfold holeTotal tripTotal lenTotal
  linarith

/-- `lem:clock`, summed: `∑_λ |λ| ≤ 3 ∑_λ EV(λ)`. -/
theorem lenTotal_le : lenTotal input ≤ 3 * evTotal input := by
  unfold lenTotal evTotal
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => lenAt_le hv i

/-- **`lem:evfetch`**: `∑_λ EV(λ) ≤ ∑_λ fetch(λ) + ∑ wᵢ`, by telescoping `∑ᵢ wᵢ xᵢ` of the base state. -/
theorem evTotal_le : evTotal input ≤ fetchTotal input + input.totalWeight := by
  have h := Finset.sum_range_sub (fun i => baseMass input (snapAt input i))
    (log input).length
  rw [Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.2.2),
    Finset.sum_sub_distrib] at h
  have hN : baseMass input (snapAt input (log input).length) ≤ input.totalWeight := by
    unfold baseMass Instance.totalWeight
    apply Finset.sum_le_sum
    intro j _
    have := ((baseState_isRest hv (log input).length).1 j).2
    have := hv.weight_pos j
    nlinarith
  have h0 : 0 ≤ baseMass input (snapAt input 0) := by
    unfold baseMass
    apply Finset.sum_nonneg
    intro j _
    have := ((baseState_isRest hv 0).1 j).1
    have := hv.weight_pos j
    have := Instance.delta_pos hv
    nlinarith
  unfold evTotal fetchTotal
  linarith

/-- **`lem:lengthfetch`**: `∑_λ |λ| ≤ 3 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem lenTotal_le_fetchTotal : lenTotal input ≤ 3 * fetchTotal input + 3 * input.totalWeight := by
  have h2 := lenTotal_le hv
  have h3 := evTotal_le hv
  linarith

/-- The payments from the budgets are at most `3 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem holeTotal_add_tripTotal_le' :
    holeTotal input + tripTotal input ≤ 3 * fetchTotal input + 3 * input.totalWeight := by
  have h1 := holeTotal_add_tripTotal_le hv
  have h2 := lenTotal_le_fetchTotal hv
  linarith

/-! ### The fetch cost and the length of the output -/

/-- The fetch cost of `PMD` is at most the fetches of the critical services plus the payments for holes and round trips. -/
theorem fetchCost_le_preempt :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      fetchTotal input + holeTotal input + tripTotal input := by
  have hsum := sum_open_eq_close hv
  have hpay := Finset.sum_le_sum fun i (_ : i ∈ Finset.range (log input).length) =>
    openAt_le_holeAt hv i
  rw [fetchCost_output hv,
    Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).1)]
  simp only [Finset.sum_add_distrib]
  unfold fetchTotal holeTotal tripTotal
  linarith

/-- The fetch cost of `PMD` is at least the fetches of the critical services plus the costs of the round trips, i.e. of all visits (used in `prop:algdelay`). -/
theorem fetchTotal_add_tripTotal_le_fetchCost :
    fetchTotal input + tripTotal input ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) := by
  have hclose := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (log input).length) =>
    closeAt_nonneg hv i
  rw [fetchCost_output hv,
    Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).1)]
  simp only [Finset.sum_add_distrib]
  unfold fetchTotal tripTotal
  linarith

/-- **`prop:preemptfetch`**: the fetch cost of `PMD` is at most `∑_λ fetch(λ) + ∑_λ |λ|`. -/
theorem fetchCost_le_lenTotal :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      fetchTotal input + lenTotal input := by
  have h0 := fetchCost_le_preempt hv
  have h1 := holeTotal_add_tripTotal_le hv
  linarith

/-- **`prop:preemptfetch` + `lem:lengthfetch`**: the fetch cost of `PMD` is at most `4 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem fetchCost_le :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      4 * fetchTotal input + 3 * input.totalWeight := by
  have h0 := fetchCost_le_preempt hv
  have h1 := holeTotal_add_tripTotal_le' hv
  linarith

end

end

end CostProof

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

/-! ## Inlined from `PagingWithDelay.Analysis.Pending` -/
section

/-!
# Pending requests as a sub-multiset of the requests

Every request value occurs in the pending list at most as often as among the requests (a tick adds all requests with a fresh arrival time, which no pending request has). Hence sums over the pending list are bounded by index sums over the requests whose value is pending.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace PendingProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

open Classical

/-- Every request value is pending at most as often as it occurs in the requests. -/
theorem pending_count_le (hv : input.Valid) (i : ℕ) (ρ : Request Page) :
    (snapAt input i).pending.count ρ ≤ input.requests.count ρ := by
  induction i with
  | zero => rw [snapAt_zero hv]; simp [initialSnap]
  | succ i ih =>
    by_cases hi : i < (log input).length
    · rcases hm : moveAt i hi with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
      · obtain ⟨-, -, -, hup, heq⟩ := tick_spec hv hi hm
        rw [heq]
        refine (List.filter_sublist.count_le _).trans ?_
        rw [List.count_append]
        by_cases ha : ρ.arrival = t
        · have h0 : (snapAt input i).pending.count ρ = 0 := by
            rw [List.count_eq_zero]
            intro hρ
            exact (pending_spec hv hρ).2.2 (by rw [hup, ha]; simp)
          rw [h0, zero_add]
          exact List.filter_sublist.count_le _
        · have h0 : (input.requests.filter fun ρ => decide (ρ.arrival = t)).count ρ = 0 := by
            rw [List.count_eq_zero]
            intro hρ
            exact ha (by simpa using (List.mem_filter.mp hρ).2)
          rw [h0, add_zero]
          exact ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [(critical_spec hv hi hm).2.2]
        exact (List.filter_sublist.count_le _).trans ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [(trip_spec hv hi hm).2.2.2]
        exact (List.filter_sublist.count_le _).trans ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
    · rw [snapAt_of_ge (by omega)]
      rw [snapAt_of_ge (by omega)] at ih
      exact ih

/-- A sum of nonnegative terms over the pending requests satisfying `P` is at most the sum over the indices of the requests whose value is pending and satisfies `P`. -/
theorem sum_pending_le (hv : input.Valid) (i : ℕ) (P : Request Page → Prop)
    (f : Request Page → ℝ) (hf : ∀ ρ ∈ input.requests, 0 ≤ f ρ) :
    (((snapAt input i).pending.filter fun ρ => decide (P ρ)).map f).sum ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ P input.requests[k]),
        f input.requests[k] := by
  set L := (snapAt input i).pending.filter fun ρ => decide (P ρ) with hL
  set R := input.requests with hR
  set g : Request Page → ℝ := fun ρ => if ρ ∈ (snapAt input i).pending ∧ P ρ then f ρ else 0
    with hg
  have hrhs : ∑ k ∈ Finset.univ.filter (fun k : Fin R.length =>
      R[k] ∈ (snapAt input i).pending ∧ P R[k]), f R[k] = (R.map g).sum := by
    rw [Finset.sum_filter]
    exact Fin.sum_univ_fun_getElem R g
  rw [hrhs, Finset.sum_list_map_count, Finset.sum_list_map_count]
  have hmemL : ∀ ρ, ρ ∈ L ↔ ρ ∈ (snapAt input i).pending ∧ P ρ := by
    intro ρ; rw [hL, List.mem_filter, decide_eq_true_iff]
  have hsub : L.toFinset ⊆ R.toFinset := by
    intro ρ hρ
    rw [List.mem_toFinset, hmemL] at hρ
    rw [List.mem_toFinset]
    exact (pending_spec hv hρ.1).1
  calc ∑ ρ ∈ L.toFinset, L.count ρ • f ρ ≤ ∑ ρ ∈ L.toFinset, R.count ρ • g ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [List.mem_toFinset] at hρ
        have hρ' := (hmemL ρ).mp hρ
        have hgρ : g ρ = f ρ := by rw [hg]; simp [hρ']
        rw [hgρ, nsmul_eq_mul, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hf ρ (pending_spec hv hρ'.1).1)
        exact_mod_cast (List.filter_sublist.count_le _).trans (pending_count_le hv i ρ)
    _ = ∑ ρ ∈ R.toFinset, R.count ρ • g ρ := by
        apply Finset.sum_subset hsub
        intro ρ _ hρ
        rw [List.mem_toFinset, hmemL] at hρ
        rw [hg]; simp [hρ]

/-- The delay of the pending requests on `p` at a time `t ≥` their arrivals is at most the index sum of their delays. -/
theorem pageDelay_le_sum (hv : input.Valid) (i : ℕ) (p : Page) (t : ℝ)
    (ht : ∀ ρ ∈ (snapAt input i).pending, ρ.arrival ≤ t) :
    pageDelay (snapAt input i).pending p t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = p),
        input.requests[k].delay (t - input.requests[k].arrival) := by
  set f : Request Page → ℝ := fun ρ => if ρ.arrival ≤ t then ρ.delay (t - ρ.arrival) else 0
    with hfdef
  have hf : ∀ ρ ∈ input.requests, 0 ≤ f ρ := by
    intro ρ hρ
    rw [hfdef]
    try dsimp only
    split_ifs with h
    · rw [← hv.delay_zero ρ hρ]
      exact hv.delay_mono ρ hρ (by linarith)
    · exact le_rfl
  have key := sum_pending_le hv i (fun ρ => ρ.page = p) f hf
  have hl : pageDelay (snapAt input i).pending p t =
      (((snapAt input i).pending.filter fun ρ => decide (ρ.page = p)).map f).sum := by
    unfold pageDelay
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    rw [hfdef]
    try simp only
    rw [if_pos (ht ρ (List.mem_filter.mp hρ).1)]
  have hfil : ((snapAt input i).pending.filter fun ρ => decide (ρ.page = p)) =
      (snapAt input i).pending.filter fun ρ => @decide (ρ.page = p) (Classical.propDecidable _) :=
    List.filter_congr (fun ρ _ => decide_eq_decide.mpr Iff.rfl)
  rw [hl, hfil]
  refine key.trans (le_of_eq ?_)
  refine Finset.sum_congr (by ext k; simp only [Finset.mem_filter]) ?_
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [hfdef]
  try simp only
  rw [if_pos (ht _ hk.2.1)]

end PendingProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.Chargeable` -/
section

/-!
# Chargeable visits (`lem:miss`, `lem:chargeable`)

* `missW_le_chargeW` (`lem:miss`): every miss service is chargeable. By the trigger, the pending requests on its page `p` have delay at least `w_p`; either the comparator has served one of them (and `p`, not cached, was evicted since: (i)), or none is served yet, so each has comparator delay cost at least its current delay (ii).
* `sum_chargeW_le` (`lem:chargeable`): the chargeable visits weigh at most `fetchCost(S) + w(C₀) + ∑_ρ d_ρ(σ ρ - a_ρ)`. Visits with (i) are charged to the comparator's last eviction of their page (distinct for distinct visits); visits with (ii) to the comparator's delay cost of their pending requests (disjoint for distinct visits).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace TeleProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState)
open PagingWithDelay.Schedule (cacheAt evictedAt fetchedAt SwapForm ServedBy IsLastEviction)

open Finset Classical

variable {input : Instance Page} {σ : Request Page → ℝ} {S : Schedule Page}

/-! ### Elementary facts -/

theorem visitPage_lt {i : ℕ} {p : Page} (h : visitPage input i = some p) :
    i < (log input).length := by
  by_contra hi
  simp [visitPage, dif_neg hi] at h

open scoped InstanceNotation in
theorem chargeW_of_chargeable {i : ℕ} {p : Page} (hc : IsChargeable input σ S i)
    (hp : visitPage input i = some p) : chargeW input σ S i = w p := by
  unfold chargeW
  rw [if_pos hc, hp]

theorem chargeW_of_not_chargeable {i : ℕ} (hc : ¬ IsChargeable input σ S i) :
    chargeW input σ S i = 0 := by
  unfold chargeW
  rw [if_neg hc]

theorem chargeW_nonneg (hv : input.Valid) (i : ℕ) : 0 ≤ chargeW input σ S i := by
  unfold chargeW
  split_ifs
  · split
    · exact (hv.weight_pos _).le
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_nonneg (hv : input.Valid) (i : ℕ) : 0 ≤ tripChargeW input σ S i := by
  unfold tripChargeW
  split_ifs with hi
  · split
    · exact chargeW_nonneg hv i
    · exact le_rfl
  · exact le_rfl

/-- A visit of `p` serves all pending requests on `p`. -/
theorem not_pending_of_visit (hv : input.Valid) {i : ℕ} {p : Page}
    (hp : visitPage input i = some p) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (i + 1)).pending) : ρ.page ≠ p := by
  have hi := visitPage_lt hp
  unfold visitPage at hp
  rw [dif_pos hi] at hp
  revert hp
  cases hmv : moveAt i hi with
  | critical q =>
    intro hp
    cases hp
    exact ((pending_succ_of_critical hv hi hmv).1 hρ).2
  | trip e π =>
    intro hp
    cases hp
    exact ((pending_succ_of_trip hv hi hmv).1 hρ).2
  | _ => intro hp; cases hp

/-- A request pending at a visit of its page is not pending at any later entry. -/
theorem not_pending_after_visit (hv : input.Valid) {i i' : ℕ} (hii' : i < i') {p : Page}
    (hp : visitPage input i = some p) {ρ : Request Page}
    (ha : ρ.arrival ≤ entryTime input i) (hρ' : ρ ∈ (snapAt input i').pending) :
    ρ.page ≠ p :=
  not_pending_of_visit hv hp (pending_of_later hv hii' hρ' ha)

/-- In swap form, a step evicts at most one page. -/
theorem evicted_unique' {I : Instance Page} (hS : SwapForm I S) {j : ℕ}
    (hj : j < S.length) {p q : Page} (hp : p ∈ evictedAt I S j) (hq : q ∈ evictedAt I S j) :
    p = q := by
  obtain ⟨a, b, ha, hb, hcache⟩ := hS.swap j hj
  have hsucc : Schedule.cacheBeforeStep I S (j + 1) = S[j].cache := by
    simp [Schedule.cacheBeforeStep, List.getElem?_eq_getElem hj]
  unfold evictedAt at hp hq
  rw [hsucc, hcache] at hp hq
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hp hq
  have h1 : p = b := by by_contra hne; exact hp.2.2 hne hp.1
  have h2 : q = b := by by_contra hne; exact hq.2.2 hne hq.1
  rw [h1, h2]

/-! ### `lem:miss` -/

/-- `lem:miss`: a miss service is chargeable, so `missW ≤ chargeW`. -/
theorem missW_le_chargeW (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (hF : S.FeasibleBy input σ) (i : ℕ) :
    missW input S i ≤ chargeW input σ S i := by
  by_cases hi : i < (log input).length
  swap
  · have : missW input S i = 0 := by simp only [missW, dif_neg hi]
    rw [this]; exact chargeW_nonneg hv i
  cases hmv : moveAt i hi with
  | critical p =>
    have hmw : missW input S i =
        if p ∈ cacheAt input S (entryTime input i) then 0
        else input.weight p := by
      simp only [missW, dif_pos hi, hmv]
    rw [hmw]
    split_ifs with hrO
    · exact chargeW_nonneg hv i
    have hvp : visitPage input i = some p := by simp only [visitPage, dif_pos hi, hmv]
    refine le_of_eq (chargeW_of_chargeable ⟨p, hvp, ?_⟩ hvp).symm
    by_cases hserved : ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
        ServedBy input σ S ρ (entryTime input i)
    · exact Or.inl ⟨hrO, hserved⟩
    right
    push_neg at hserved
    obtain ⟨htrig, -, -, -, hti⟩ := critical_facts hv hi hmv
    have h1 : (snapAt input i).claims p + input.weight p ≤
        pageDelay (snapAt input i).pending p (snapAt input i).now := htrig.1
    have h0 := claims_nonneg hv i p
    have h2 := PendingProof.pageDelay_le_sum hv i p (snapAt input i).now
      (fun ρ hρ => (pending_spec hv hρ).2.1)
    have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = p),
        input.requests[k].delay ((snapAt input i).now - input.requests[k].arrival) ≤
        optDelayOn input σ (snapAt input i) p := by
      unfold optDelayOn
      refine sum_le_sum fun k hk => ?_
      rw [mem_filter] at hk
      have hn := hserved _ hk.2.1 hk.2.2
      rw [hti] at hn
      exact Schedule.delay_le_of_not_servedBy' hF hv k hn
    linarith
  | _ =>
    have : missW input S i = 0 := by simp only [missW, dif_pos hi, hmv]
    rw [this]; exact chargeW_nonneg hv i

/-! ### `lem:chargeable` -/

/-- Condition (i) of `def:chargeable` at entry `i`. -/
def CondI (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) : Prop :=
  ∃ p, visitPage input i = some p ∧
    p ∉ cacheAt input S (entryTime input i) ∧
    ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
      ServedBy input σ S ρ (entryTime input i)

section Charge

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hSw : SwapForm input S)
  (hF : S.FeasibleBy input σ)
include hv hσ hSw hF

open scoped InstanceNotation in
/-- The visits with (i) weigh at most the comparator's evicted weight. -/
theorem sum_condI_le :
    ∑ i ∈ (range (log input).length).filter (CondI input σ S), chargeW input σ S i ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p := by
  set A := (range (log input).length).filter (CondI input σ S) with hA
  have H : ∀ i ∈ A, ∃ j, ∃ p, visitPage input i = some p ∧
      chargeW input σ S i = w p ∧
      IsLastEviction input S p (entryTime input i) j ∧
      ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
        ∃ hj : j < S.length, ρ.arrival ≤ S[j].time := by
    intro i hi
    obtain ⟨-, p, hvp, hrO, ρ, hρ, hρp, hsv⟩ := mem_filter.1 hi
    have hcw := chargeW_of_chargeable (Or.inl ⟨hrO, ρ, hρ, hρp, hsv⟩ |> fun h => ⟨p, hvp, h⟩) hvp
    subst hρp
    obtain ⟨j, hj, hj'⟩ := Schedule.exists_lastEviction hv hSw hF hsv hrO
    exact ⟨j, ρ.page, hvp, hcw, hj, ρ, hρ, rfl, hj'⟩
  choose! jOf hjOf using H
  set F : ℕ → ℝ := fun j => ∑ p ∈ evictedAt input S j, w p
    with hFdef
  have hF0 : ∀ j, 0 ≤ F j := fun j => sum_nonneg fun p _ => (hv.weight_pos p).le
  have h1 : ∑ i ∈ A, chargeW input σ S i ≤ ∑ i ∈ A, F (jOf i) := by
    apply sum_le_sum
    intro i hi
    obtain ⟨p, -, hcw, ⟨-, -, hev, -⟩, -⟩ := hjOf i hi
    rw [hcw]
    exact single_le_sum (f := fun p => w p) (fun p _ => (hv.weight_pos p).le) hev
  have hinj_lt : ∀ i ∈ A, ∀ i' ∈ A, i < i' → jOf i ≠ jOf i' := by
    intro i hi i' hi' hlt heq
    obtain ⟨p, hvp, -, ⟨hj, ht, hev, -⟩, -⟩ := hjOf i hi
    obtain ⟨p', -, -, ⟨-, -, hev', -⟩, ρ', hρ', hρp', hj', ha'⟩ := hjOf i' hi'
    rw [← heq] at hev'
    have ha'' : ρ'.arrival ≤ S[jOf i].time := by simpa [heq] using ha'
    have hpage : p' = p := evicted_unique' hSw hj hev' hev
    exact not_pending_after_visit hv hlt hvp (ha''.trans ht) hρ' (hρp'.trans hpage)
  have hinj : Set.InjOn jOf A := by
    intro i hi i' hi' heq
    rcases lt_trichotomy i i' with hlt | hlt | hlt
    · exact absurd heq (hinj_lt i hi i' hi' hlt)
    · exact hlt
    · exact absurd heq.symm (hinj_lt i' hi' i hi hlt)
  have h2 : ∑ i ∈ A, F (jOf i) = ∑ j ∈ A.image jOf, F j := (sum_image hinj).symm
  have h3 : ∑ j ∈ A.image jOf, F j ≤ ∑ j ∈ range S.length, F j := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
      obtain ⟨-, -, -, ⟨hj, -⟩, -⟩ := hjOf i hi
      exact mem_range.2 hj
    · intro j _ _
      exact hF0 j
  have h4 := Schedule.sum_evicted_le hv hSw
  calc ∑ i ∈ A, chargeW input σ S i ≤ ∑ i ∈ A, F (jOf i) := h1
    _ = ∑ j ∈ A.image jOf, F j := h2
    _ ≤ ∑ j ∈ range S.length, F j := h3
    _ ≤ _ := h4

/-- The chargeable visits without (i) (which satisfy (ii)) weigh at most the comparator's delay cost. -/
theorem sum_not_condI_le :
    ∑ i ∈ (range (log input).length).filter (fun i => ¬ CondI input σ S i),
        chargeW input σ S i ≤ Schedule.totalDelay input σ := by
  set R := (range (log input).length).filter (fun i => ¬ CondI input σ S i) with hR
  set C := R.filter (IsChargeable input σ S) with hC
  have hRC : ∑ i ∈ R, chargeW input σ S i = ∑ i ∈ C, chargeW input σ S i := by
    refine (sum_filter_of_ne (s := R) (p := IsChargeable input σ S) fun i _ hne => ?_).symm
    by_contra hc
    exact hne (chargeW_of_not_chargeable hc)
  have H : ∀ i ∈ C, ∃ p, visitPage input i = some p ∧
      input.weight p ≤ optDelayOn input σ (snapAt input i) p := by
    intro i hi
    obtain ⟨hiR, hc⟩ := mem_filter.1 hi
    obtain ⟨-, hnI⟩ := mem_filter.1 hiR
    obtain ⟨p, hvp, hAB⟩ := hc
    exact ⟨p, hvp, hAB.resolve_left fun hA => hnI ⟨p, hvp, hA⟩⟩
  have : Nonempty Page := Fintype.card_pos_iff.mp (by have := hv.cacheSize_lt; omega)
  choose! pOf hpOf using H
  set I : ℕ → Finset (Fin input.requests.length) := fun i =>
    Finset.univ.filter (fun k : Fin input.requests.length =>
      input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = pOf i) with hI
  have hdisj : (C : Set ℕ).PairwiseDisjoint I := by
    have key : ∀ i ∈ C, ∀ i' ∈ C, i < i' → Disjoint (I i) (I i') := by
      intro i hi i' hi' hlt
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [hI, mem_filter, mem_univ, true_and] at hk hk'
      have ha : input.requests[k].arrival ≤ entryTime input i :=
        (pending_spec hv hk.1).2.1.trans (now_le_entryTime hv i)
      exact not_pending_after_visit hv hlt (hpOf i hi).1 ha hk'.1 hk.2
    intro i hi i' hi' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i hi i' hi' hlt
    · exact (key i' hi' i hi hlt).symm
  rw [hRC]
  refine Schedule.sum_le_totalDelay hv hσ C I hdisj (fun i => chargeW input σ S i) ?_
  intro i hi
  obtain ⟨hvp, hle⟩ := hpOf i hi
  try dsimp only
  rw [chargeW_of_chargeable (mem_filter.1 hi).2 hvp]
  exact hle

open scoped InstanceNotation in
/-- `lem:chargeable`: the chargeable visits weigh at most `fetchCost(S) + w(C₀) + ∑_ρ d_ρ(σ ρ - a_ρ)`. -/
theorem sum_chargeW_le :
    ∑ i ∈ range (log input).length, chargeW input σ S i ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p +
        Schedule.totalDelay input σ := by
  rw [← sum_filter_add_sum_filter_not (range (log input).length) (CondI input σ S)]
  have := sum_condI_le hv hσ hSw hF
  have := sum_not_condI_le hv hσ hSw hF
  linarith

end Charge

end TeleProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.NotOverdue` -/
section

/-!
# Services that are not overdue (`lem:timely`)

The excess of the critical services that are not overdue is at most `L` times the comparator's delay cost: `∑_{λ not overdue} Exc(λ) ≤ L · ∑_ρ d_ρ(σ ρ - a_ρ)`.

* A critical service `λ` on `p` claims `claimAt i q = c_q' - c_q ≥ 0` from every page `q` (`claimUpdate`), in total `|λ|/L` since `p` triggers; and `Exc(λ) ≤ |λ|`. So `Exc(λ) ≤ L ∑_q claimAt i q` (`excessAt_le`).
* Fix a page `q`. Every entry `i` that is not overdue and claims a positive amount from `q` has `q` pending, so `q` is visited at some entry `≥ i`; let `nextVisit i q` be the first one, and group the claims from `q` by `(q, nextVisit i q)`. Let `m` be the last entry of a group. Within the group no visit of `q` resets `c_q`, so the claims telescope to at most `c_q + claimAt m q ≤ delay_q(t_m) - w_q` right before `m` (a positive claim is at most the overshoot `delay_q - c_q - w_q`). As `m` is not overdue and `w_q ≤ w_{p_m}`, the pending requests on `q` served by the comparator have delay at most `w_q`; every other one costs the comparator at least its current delay. So the group is paid by the comparator's delay cost of the requests pending on `q` right before `m` (`group_le`).
* These request sets are pairwise disjoint: a request pending on `q` before `m(q, j)` and before `m(q, j')` with `j < j'` would still be pending after the visit `j` of `q` (`group_disjoint`).

**Remark on the paper.** The paper's argument goes through as stated. Our `IsOverdue` is not restricted to miss services on pages below `w_min(OPT)`, which the argument does not need. The telescoping only uses the claims between the first and the last grouped entry, not that `c_q` is reset to `0` at the previous visit.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace NotOverdueProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd)
open PagingWithDelay.Schedule (cacheAt ServedBy)

open Classical

noncomputable section

variable (input : Instance Page)

/-- The amount entry `i` claims from page `q`: if it is a critical service on `p`, the increase `claimUpdate … q - c_q` of `c_q`; else `0`. -/
def claimAt (i : ℕ) (q : Page) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q - (snapAt input i).claims q
    | _ => 0
  else 0

/-- The first visit of `q` at or after entry `i` (`0` if there is none). -/
def nextVisit (i : ℕ) (q : Page) : ℕ :=
  if h : ∃ j, i ≤ j ∧ visitPage input j = some q then Nat.find h else 0

variable {input}

/-! ### Claims -/

theorem claimAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (q : Page) :
    claimAt input i q = claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q - (snapAt input i).claims q := by
  simp only [claimAt, dif_pos h, hm]

theorem claimAt_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) (q : Page) : claimAt input i q = 0 := by
  unfold claimAt
  rw [dif_pos h]
  split
  · next p hp => exact absurd hp (hm p)
  · rfl

theorem claimAt_of_ge {i : ℕ} (h : (log input).length ≤ i) (q : Page) :
    claimAt input i q = 0 := by
  unfold claimAt
  rw [dif_neg (by omega)]

theorem visitPage_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) : visitPage input i = some p := by
  simp only [visitPage, dif_pos h, hm]

theorem visitPage_of_trip {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) : visitPage input i = some π.page := by
  simp only [visitPage, dif_pos h, hm]

theorem visitPage_of_other {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π) :
    visitPage input i = none := by
  unfold visitPage
  rw [dif_pos h]
  split
  · next p hp => exact absurd hp (hc p)
  · next e π hp => exact absurd hp (ht e π)
  · rfl

theorem lt_of_visitPage {i : ℕ} {q : Page} (hq : visitPage input i = some q) :
    i < (log input).length := by
  by_contra hge
  unfold visitPage at hq
  rw [dif_neg hge] at hq
  cases hq

section

variable (hv : input.Valid)
include hv

theorem claimAt_nonneg (i : ℕ) (q : Page) : 0 ≤ claimAt input i q := by
  by_cases h : i < (log input).length
  · by_cases hc : ∃ p, moveAt i h = .critical p
    · obtain ⟨p, hm⟩ := hc
      rw [claimAt_of_critical h hm]
      linarith [le_claimUpdate hv (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q]
    · push_neg at hc
      rw [claimAt_of_not_critical h hc]
  · rw [claimAt_of_ge (by omega)]

open scoped InstanceNotation in
/-- A critical service claims `|λ|/L` in total. -/
theorem sum_claimAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    ∑ q, claimAt input i q = serviceEnd input (snapAt input i).x p / L := by
  simp_rw [claimAt_of_critical h hm]
  exact sum_claimUpdate_of_triggered hv (critical_facts hv h hm).1

open scoped InstanceNotation in
/-- `|λ| = L · ∑_q claimAt i q`. -/
theorem lenAt_eq (i : ℕ) : lenAt input i = L * ∑ q, claimAt input i q := by
  by_cases h : i < (log input).length
  · by_cases hc : ∃ p, moveAt i h = .critical p
    · obtain ⟨p, hm⟩ := hc
      rw [sum_claimAt_of_critical hv h hm, mul_div_cancel₀ _ (Instance.L_pos hv).ne']
      simp only [lenAt, dif_pos h, hm]
    · push_neg at hc
      simp_rw [claimAt_of_not_critical h hc]
      simp only [Finset.sum_const_zero, mul_zero]
      unfold lenAt
      rw [dif_pos h]
      split
      · next p hp => exact absurd hp (hc p)
      · rfl
  · simp_rw [claimAt_of_ge (show (log input).length ≤ i by omega)]
    simp only [Finset.sum_const_zero, mul_zero]
    unfold lenAt
    rw [dif_neg h]

/-- `Exc(λ) ≤ |λ|`. -/
theorem excessAt_le_lenAt (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) :
    excessAt input S i ≤ lenAt input i := by
  unfold excessAt lenAt
  by_cases h : i < (log input).length
  · rw [dif_pos h, dif_pos h]
    split
    · next p hp =>
      split_ifs
      · exact serviceEnd_nonneg' (input := input) _ _
      · refine le_trans ?_ (sum_levelLen_Icc_le (snapAt input i).x p (level input p)
          (maxLevel input))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun e _ _ => levelLen_nonneg hv _ _ _
    · exact le_rfl
  · rw [dif_neg h, dif_neg h]

open scoped InstanceNotation in
/-- `Exc(λ) ≤ L ∑_q claimAt i q`. -/
theorem excessAt_le (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) :
    excessAt input S i ≤ L * ∑ q, claimAt input i q :=
  (lenAt_eq hv i) ▸ excessAt_le_lenAt hv σ S i

/-- Off visits of `q`, `c_q` changes exactly by the claim from `q`. -/
theorem claims_succ {i : ℕ} {q : Page} (hq : visitPage input i ≠ some q) :
    (snapAt input (i + 1)).claims q = (snapAt input i).claims q + claimAt input i q := by
  by_cases h : i < (log input).length
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · have hpq : q ≠ p := by
        rintro rfl; exact hq (visitPage_of_critical h hm)
      rw [(critical_spec hv h hm).2.2, claimAt_of_critical h hm]
      simp only [Function.update_of_ne hpq]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · have hpq : q ≠ π.page := by
        intro he; exact hq (he ▸ visitPage_of_trip h hm)
      rw [(trip_spec hv h hm).2.2.2, claimAt_of_not_critical h (by rw [hm]; simp)]
      simp only [Function.update_of_ne hpq]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega), claimAt_of_ge (by omega)]
    ring

/-- Telescoping of `c_q` over entries without a visit of `q`. -/
theorem claims_telescope {a b : ℕ} (hab : a ≤ b) {q : Page}
    (hno : ∀ l, a ≤ l → l < b → visitPage input l ≠ some q) :
    (snapAt input b).claims q =
      (snapAt input a).claims q + ∑ l ∈ Finset.Ico a b, claimAt input l q := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [claims_succ hv (hno b hab (by omega)), ih fun l h1 h2 => hno l h1 (by omega),
      Finset.sum_Ico_succ_top hab]
    ring

/-- A visit of `q` serves all pending requests on `q`. -/
theorem not_pending_succ_of_visit {j : ℕ} {q : Page} (hj : visitPage input j = some q)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input (j + 1)).pending) : ρ.page ≠ q := by
  have h := lt_of_visitPage hj
  by_cases hc : ∃ p, moveAt j h = .critical p
  · obtain ⟨p, hm⟩ := hc
    rw [visitPage_of_critical h hm] at hj
    cases hj
    exact ((pending_succ_of_critical hv h hm).1 hρ).2
  by_cases ht : ∃ e π, moveAt j h = .trip e π
  · obtain ⟨e, π, hm⟩ := ht
    rw [visitPage_of_trip h hm] at hj
    cases hj
    exact ((pending_succ_of_trip hv h hm).1 hρ).2
  push_neg at hc ht
  rw [visitPage_of_other h hc ht] at hj
  cases hj

/-- A pending request on `q` is eventually removed by a visit of `q`. -/
theorem exists_visit {i : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input i).pending) :
    ∃ j, i ≤ j ∧ visitPage input j = some ρ.page := by
  have hi : i ≤ (log input).length := by
    by_contra hgt
    rw [snapAt_of_ge (by omega), ← snapAt_of_ge (input := input) le_rfl,
      (final_spec hv).2.1] at hρ
    simp at hρ
  have hfin : ρ ∉ (snapAt input (log input).length).pending := by
    rw [(final_spec hv).2.1]; simp
  obtain ⟨j, hj1, hj2, hPj, hPj1⟩ :=
    exists_drop (fun m => ρ ∈ (snapAt input m).pending) hρ hfin hi
  refine ⟨j, hj1, ?_⟩
  rcases (pending_removed hv hj2 hPj hPj1).1 with hm | ⟨e, π, hm, hπ⟩
  · exact visitPage_of_critical hj2 hm
  · rw [← hπ]; exact visitPage_of_trip hj2 hm

theorem nextVisit_spec {i : ℕ} {q : Page} (hex : ∃ j, i ≤ j ∧ visitPage input j = some q) :
    i ≤ nextVisit input i q ∧ visitPage input (nextVisit input i q) = some q ∧
      ∀ l, i ≤ l → l < nextVisit input i q → visitPage input l ≠ some q := by
  unfold nextVisit
  rw [dif_pos hex]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun l h1 h2 h3 => ?_⟩
  exact Nat.find_min hex h2 ⟨h1, h3⟩

open scoped InstanceNotation in
/-- The facts behind a positive claim from `q`: entry `i` is a critical service on a page `p` with `w_q ≤ w_p`, `q` has a pending request, and `c_q + claimAt i q` is at most `delay_q - w_q`. -/
theorem claim_pos_facts {i : ℕ} {q : Page} (hpos : 0 < claimAt input i q) :
    ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧
      w q ≤ w p ∧
      (∃ ρ ∈ (snapAt input i).pending, ρ.page = q) ∧
      (snapAt input i).claims q + claimAt input i q ≤
        pageDelay (snapAt input i).pending q (snapAt input i).now - w q := by
  have h : i < (log input).length := by
    by_contra hge; rw [claimAt_of_ge (by omega)] at hpos; exact lt_irrefl 0 hpos
  have hc : ∃ p, moveAt i h = .critical p := by
    by_contra hno; push_neg at hno
    rw [claimAt_of_not_critical h hno] at hpos; exact lt_irrefl 0 hpos
  obtain ⟨p, hm⟩ := hc
  set s := snapAt input i
  have hcl := claimAt_of_critical h hm q
  have hle := claimUpdate_le (input := input) s.x s.pending s.claims s.now p q
  have hlight : w q ≤ w p := by
    by_contra hn
    have := claimUpdate_of_not_lighter (input := input) s.x s.pending s.claims s.now
      (p := p) (q := q) (by rw [mem_lighter]; exact hn)
    rw [this, sub_self] at hcl
    rw [hcl] at hpos; exact lt_irrefl 0 hpos
  have hov : 0 < overshoot input s.pending s.claims q s.now := by linarith
  have hlt := overshoot_pos_iff.1 hov
  have hcq := claims_nonneg hv i q
  have hw := hv.weight_pos q
  refine ⟨h, p, hm, hlight, ?_, ?_⟩
  · exact exists_pending_of_pageDelay_ne (t := s.now) (by intro h0; linarith)
  · have hov' : overshoot input s.pending s.claims q s.now =
        pageDelay s.pending q s.now - s.claims q - w q := by
      unfold overshoot; exact max_eq_right (by linarith)
    linarith

end

/-! ### Grouping the claims against the comparator -/

/-- Splitting the page delay into the requests satisfying `P` and the others. -/
theorem pageDelay_split (l : List (Request Page)) (q : Page) (t : ℝ) (P : Request Page → Prop) :
    pageDelay l q t =
      ((l.filter fun ρ => decide (ρ.page = q ∧ P ρ)).map fun ρ => ρ.delay (t - ρ.arrival)).sum +
      ((l.filter fun ρ => decide (ρ.page = q ∧ ¬ P ρ)).map fun ρ => ρ.delay (t - ρ.arrival)).sum := by
  unfold pageDelay
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hq : a.page = q <;> by_cases hP : P a <;>
      simp [hq, hP, ih] <;> ring

variable (input) (σ : Request Page → ℝ) (S : Schedule Page)

/-- The entries that are not overdue and claim a positive amount from `q`. -/
def claimSet (q : Page) : Finset ℕ :=
  (Finset.range (log input).length).filter fun i =>
    ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q

/-- The entries of `claimSet q` whose next visit of `q` is entry `j`. -/
def groupSet (q : Page) (j : ℕ) : Finset ℕ :=
  (claimSet input σ S q).filter fun i => nextVisit input i q = j

/-- The last entry of the group `(q, j)`. -/
def lastOf (q : Page) (j : ℕ) : ℕ := (groupSet input σ S q j).sup id

/-- The requests (by index) that pay for the group `(q, j)`: those pending on `q` right before its last entry. -/
def groupReq (q : Page) (j : ℕ) : Finset (Fin input.requests.length) :=
  Finset.univ.filter fun k => (groupSet input σ S q j).Nonempty ∧
    input.requests[k] ∈ (snapAt input (lastOf input σ S q j)).pending ∧
    input.requests[k].page = q

variable {input σ S}

section Comparator

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hF : S.FeasibleBy input σ)
include hv

theorem mem_claimSet_facts {q : Page} {i : ℕ} (hi : i ∈ claimSet input σ S q) :
    i < (log input).length ∧ ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q ∧
      ∃ j, i ≤ j ∧ visitPage input j = some q := by
  simp only [claimSet, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨-, -, -, -, ⟨ρ, hρ, hρq⟩, -⟩ := claim_pos_facts hv hi.2.2
  obtain ⟨j, hj1, hj2⟩ := exists_visit hv hρ
  exact ⟨hi.1, hi.2.1, hi.2.2, j, hj1, hρq ▸ hj2⟩

theorem mem_groupSet_facts {q : Page} {j i : ℕ} (hi : i ∈ groupSet input σ S q j) :
    i < (log input).length ∧ ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q ∧
      i ≤ j ∧ visitPage input j = some q ∧
      ∀ l, i ≤ l → l < j → visitPage input l ≠ some q := by
  simp only [groupSet, Finset.mem_filter] at hi
  obtain ⟨h1, h2, h3, hex⟩ := mem_claimSet_facts hv hi.1
  obtain ⟨n1, n2, n3⟩ := nextVisit_spec hv hex
  rw [hi.2] at n1 n2 n3
  exact ⟨h1, h2, h3, n1, n2, n3⟩

theorem lastOf_mem {q : Page} {j : ℕ} (hne : (groupSet input σ S q j).Nonempty) :
    lastOf input σ S q j ∈ groupSet input σ S q j := by
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  unfold lastOf; rw [heq]; exact hm

theorem le_lastOf {q : Page} {j i : ℕ} (hi : i ∈ groupSet input σ S q j) :
    i ≤ lastOf input σ S q j :=
  Finset.le_sup (f := id) hi

/-- The request sets of distinct groups of the same page are disjoint. -/
theorem group_disjoint {q : Page} {j j' : ℕ} (hjj : j < j') {ρ : Request Page}
    (hne : (groupSet input σ S q j).Nonempty) (hne' : (groupSet input σ S q j').Nonempty)
    (hρ : ρ ∈ (snapAt input (lastOf input σ S q j)).pending)
    (hρ' : ρ ∈ (snapAt input (lastOf input σ S q j')).pending) (hρq : ρ.page = q) : False := by
  set m := lastOf input σ S q j
  set m' := lastOf input σ S q j'
  obtain ⟨-, -, -, hmj, hvj, -⟩ := mem_groupSet_facts hv (lastOf_mem hv hne)
  obtain ⟨-, -, -, hmj', -, hno'⟩ := mem_groupSet_facts hv (lastOf_mem hv hne')
  have hjm' : j < m' := by
    by_contra hle
    exact hno' j (by omega) hjj hvj
  have harr : ρ.arrival ≤ entryTime input j := by
    have h1 := (pending_spec hv hρ).2.1
    have h2 := now_mono hv (input := input) (show m ≤ j + 1 by omega)
    unfold entryTime
    linarith
  have hpend := pending_of_later hv hjm' hρ' harr
  exact not_pending_succ_of_visit hv hvj hpend hρq

include hσ hF

/-- The claims of a group are paid by the comparator's delay cost of its requests. -/
theorem group_le (q : Page) (j : ℕ) :
    ∑ i ∈ groupSet input σ S q j, claimAt input i q ≤
      Schedule.delayCostOn input σ (groupReq input σ S q j) := by
  by_cases hne : (groupSet input σ S q j).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact Schedule.delayCostOn_nonneg hv hσ _
  set A := groupSet input σ S q j with hA
  set m := lastOf input σ S q j with hm_def
  have hmA : m ∈ A := lastOf_mem hv hne
  set i0 := A.min' hne with hi0_def
  have hi0A : i0 ∈ A := Finset.min'_mem A hne
  obtain ⟨hmlen, hmov, hmpos, hmj, -, -⟩ := mem_groupSet_facts hv hmA
  obtain ⟨-, -, -, -, -, hi0no⟩ := mem_groupSet_facts hv hi0A
  have hi0m : i0 ≤ m := le_lastOf hv hi0A
  -- the claims of the group telescope
  have hsub : A ⊆ Finset.Ico i0 (m + 1) := by
    intro i hi
    have h1 : i0 ≤ i := Finset.min'_le A i hi
    have h2 : i ≤ m := le_lastOf hv hi
    simp only [Finset.mem_Ico]; omega
  have hstep1 : ∑ i ∈ A, claimAt input i q ≤ ∑ i ∈ Finset.Ico i0 (m + 1), claimAt input i q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => claimAt_nonneg hv i q
  rw [Finset.sum_Ico_succ_top hi0m] at hstep1
  have htel := claims_telescope hv hi0m (q := q) fun l h1 h2 => hi0no l h1 (by omega)
  have hc0 := claims_nonneg hv i0 q
  obtain ⟨_hml, p, hmp, hlight, -, hbound⟩ := claim_pos_facts hv hmpos
  -- the comparator
  have ht : entryTime input m = (snapAt input m).now := (critical_facts hv hmlen hmp).2.2.2.2
  set t := (snapAt input m).now with ht_def
  set s := snapAt input m with hs_def
  have hserved : servedDelay input σ S s q t ≤ input.weight q := by
    by_contra hlt
    push_neg at hlt
    exact hmov ⟨hmlen, p, hmp, q, hlight, by unfold PageOverdue; rw [ht]; exact hlt⟩
  have hsplit := pageDelay_split s.pending q t
    (fun ρ => ServedBy input σ S ρ t)
  have hsd : servedDelay input σ S s q t =
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
        ServedBy input σ S ρ t)).map
          fun ρ => ρ.delay (t - ρ.arrival)).sum := rfl
  have hun1 :
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => ρ.delay (t - ρ.arrival)).sum ≤
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => Schedule.delayOf σ ρ).sum := by
    apply List.sum_le_sum
    intro ρ hρ
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    exact Schedule.delay_le_of_not_servedBy hF hv (pending_spec hv hρ.1).1 hρ.2.2
  have hun2 := PendingProof.sum_pending_le hv m
    (fun ρ => ρ.page = q ∧ ¬ ServedBy input σ S ρ t)
    (Schedule.delayOf σ) (fun ρ hρ => Schedule.delayOf_nonneg hv hσ hρ)
  have hun12 :
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => ρ.delay (t - ρ.arrival)).sum ≤
      Schedule.delayCostOn input σ (groupReq input σ S q j) := by
    refine hun1.trans (le_trans (le_of_eq ?_) (hun2.trans ?_))
    · congr 2
      exact List.filter_congr fun ρ _ => decide_eq_decide.mpr Iff.rfl
    · unfold Schedule.delayCostOn
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_filter] at hk
        unfold groupReq
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hne, hk.2.1, hk.2.2.1⟩
      · intro k _ _
        exact Schedule.delayOf_getElem_nonneg hv hσ k
  rw [← hsd] at hsplit
  linarith

/-- The claims of the entries that are not overdue total at most the comparator's delay cost. -/
theorem sum_claim_notOverdue_le :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) ≤
      Schedule.totalDelay input σ := by
  set N := Finset.range (log input).length
  have h1 : ∀ i, (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) =
      ∑ q, (if ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q then claimAt input i q else 0) := by
    intro i
    split_ifs with ho
    · symm; apply Finset.sum_eq_zero; intro q _; rw [if_neg (by tauto)]
    · apply Finset.sum_congr rfl; intro q _
      by_cases hp : 0 < claimAt input i q
      · rw [if_pos ⟨ho, hp⟩]
      · rw [if_neg (by tauto)]
        exact le_antisymm (not_lt.1 hp) (claimAt_nonneg hv i q)
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ q, ∑ i ∈ N,
      (if ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q then claimAt input i q else 0) =
      ∑ j ∈ N, ∑ i ∈ groupSet input σ S q j, claimAt input i q := by
    intro q
    rw [← Finset.sum_filter]
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := claimSet input σ S q) (t := N)
      (g := fun i => nextVisit input i q)
      (fun i hi => by
        obtain ⟨-, -, -, -, hv', -⟩ := mem_groupSet_facts hv
          (Finset.mem_filter.2 ⟨hi, rfl⟩ : i ∈ groupSet input σ S q (nextVisit input i q))
        exact Finset.mem_range.2 (lt_of_visitPage hv'))
      _
  simp_rw [h2]
  rw [← Finset.sum_product (s := (Finset.univ : Finset Page)) (t := N)
    (f := fun g => ∑ i ∈ groupSet input σ S g.1 g.2, claimAt input i g.1)]
  refine Schedule.sum_le_totalDelay hv hσ (Finset.univ ×ˢ N)
    (fun g => groupReq input σ S g.1 g.2) ?_
    (fun g => ∑ i ∈ groupSet input σ S g.1 g.2, claimAt input i g.1)
    (fun g _ => group_le hv hσ hF g.1 g.2)
  rintro ⟨q, j⟩ - ⟨q', j'⟩ - hne
  rw [Function.onFun, Finset.disjoint_left]
  intro k hk hk'
  simp only [groupReq, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  obtain ⟨hA, hk1, hk2⟩ := hk
  obtain ⟨hA', hk1', hk2'⟩ := hk'
  have hqq : q = q' := hk2.symm.trans hk2'
  subst hqq
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hjj with h | h
  · exact group_disjoint hv h hA hA' hk1 hk1' hk2
  · exact group_disjoint hv h hA' hA hk1' hk1 hk2

open scoped InstanceNotation in
/-- **`lem:timely`**: the excess of the critical services that are not overdue is at most `L` times the comparator's delay cost. -/
theorem sum_excess_notOverdue_le :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else excessAt input S i) ≤
      L * Schedule.totalDelay input σ := by
  calc ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else excessAt input S i)
      ≤ ∑ i ∈ Finset.range (log input).length,
        L * (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · simp
        · exact excessAt_le hv σ S i
    _ = L * ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ L * Schedule.totalDelay input σ :=
        mul_le_mul_of_nonneg_left (sum_claim_notOverdue_le hv hσ hF) (Instance.L_pos hv).le

end Comparator

end

end NotOverdueProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.Money` -/
section

/-!
# The budget of one level (the budget argument of `lem:periodlevel`)

For a level `e`, we compare the payments from the budget `B_W` between two log entries with the total weight of the level-`e` round trips there. If no level-`e` preemptive service runs out of candidates, each starts with `B_W ≥ 4W`, pays at most `W` for its hole and ends with `B_W < W`, so it pays less than `3/2` times the weights of its round trips (`two_pay_le`). The deposits `|λ|_W` (`levelLen`) are at most the payments plus the final budget (`sum_dep_le`). After a critical service on a page of level `≤ e`, `B_W` is below `4W` at the next such critical service (`budget_lt_of_next_critical`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

namespace ExcessProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost afterLevel Stage IsRest IsFrac levelWeight_pos
  minLevel_le)

noncomputable section

/-! ### The round-trip candidate -/

section Candidate

variable {input : Instance Page}

/-- **Tie-break of the round-trip candidate**: among the pending requests on pages of level `≤ e`, its page minimizes (deadline, `tieRank`) lexicographically. -/
theorem tripCandidate_lex {pending : List (Request Page)} {t : ℝ} {e : ℤ}
    {π : Request Page} (h : tripCandidate input pending t e = some π) :
    π ∈ pending ∧ level input π.page ≤ e ∧
      ∀ ρ ∈ pending, level input ρ.page ≤ e →
        pageDeadline input pending t π.page < pageDeadline input pending t ρ.page ∨
          (pageDeadline input pending t π.page = pageDeadline input pending t ρ.page ∧
            input.tieRank π.page ≤ input.tieRank ρ.page) := by
  unfold tripCandidate at h
  have hm := List.argmin_mem h
  simp only [List.mem_filter, decide_eq_true_eq] at hm
  refine ⟨hm.1, hm.2, fun ρ hρ hl => ?_⟩
  have hmem : ρ ∈ pending.filter (fun ρ => decide (level input ρ.page ≤ e)) := by
    simpa [List.mem_filter] using ⟨hρ, hl⟩
  have := List.le_of_mem_argmin
    (f := fun ρ : Request Page => toLex (pageDeadline input pending t ρ.page, input.tieRank ρ.page))
    hmem h
  exact (Prod.Lex.toLex_le_toLex).1 this

theorem tripCandidate_spec {pending : List (Request Page)} {t : ℝ} {e : ℤ}
    {π : Request Page} (h : tripCandidate input pending t e = some π) :
    π ∈ pending ∧ level input π.page ≤ e ∧
      ∀ ρ ∈ pending, level input ρ.page ≤ e →
        pageDeadline input pending t π.page ≤ pageDeadline input pending t ρ.page := by
  obtain ⟨hm, hl, hlex⟩ := tripCandidate_lex h
  refine ⟨hm, hl, fun ρ hρ hle => ?_⟩
  rcases hlex ρ hρ hle with h | h
  · exact h.le
  · exact h.1.le

theorem tripCandidate_ne_none {pending : List (Request Page)} {t : ℝ} {e : ℤ}
    {ρ : Request Page} (hρ : ρ ∈ pending) (hl : level input ρ.page ≤ e) :
    tripCandidate input pending t e ≠ none := by
  unfold tripCandidate
  rw [Ne, List.argmin_eq_none]
  intro h
  have : ρ ∈ pending.filter (fun ρ => decide (level input ρ.page ≤ e)) := by
    simpa [List.mem_filter] using ⟨hρ, hl⟩
  rw [h] at this
  simp at this

end Candidate

/-! ### Small run facts -/

section RunFacts

variable {input : Instance Page} (hv : input.Valid)
include hv

theorem level_le_iff' (p : Page) (e : ℤ) :
    level input p ≤ e ↔ w p ≤ levelWeight e :=
  PagingWithDelay.PMD.level_le_iff hv p e

theorem preempt_state {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) :
    (snapAt input i).x = hole input b e ∧ IsRest input b := by
  refine ⟨(x_eq_hole hv hs).1, ?_⟩
  have := baseState_isRest hv i
  unfold baseState at this
  rw [hs] at this
  exact this

theorem tripCost_nonneg_le {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) (p : Page) :
    0 ≤ tripCost input (snapAt input i).x p ∧
      tripCost input (snapAt input i).x p ≤ w p := by
  have hvb := hv
  obtain ⟨hx, hb⟩ := preempt_state hv hs
  have h1 := PagingWithDelay.PMD.hole_le_one hvb hb.1 e p
  have h2 := PagingWithDelay.PMD.le_hole hvb hb.1 e p
  have h3 := (hb.1 p).1
  have hw := hv.weight_pos p
  have hd := Instance.delta_pos hv
  unfold tripCost
  rw [hx]
  constructor
  · exact mul_nonneg hw.le (by linarith)
  · nlinarith

theorem not_idle_of_preempt {l : ℕ} {e : ℤ} {b : Page → ℝ}
    (hst : (snapAt input l).stage = .preempt e b) : (snapAt input l).stage ≠ .idle := by
  rw [hst]; simp

/-- Moves inside a preemptive service happen at the current time. -/
theorem entryTime_of_preempt {l : ℕ} {e : ℤ} {b : Page → ℝ}
    (hst : (snapAt input l).stage = .preempt e b) :
    ∃ hl : l < (log input).length, entryTime input l = (snapAt input l).now := by
  have hl := lt_length_of_stage hv (not_idle_of_preempt hv hst)
  obtain ⟨-, h1, h2⟩ := not_idle_moves hv hl (not_idle_of_preempt hv hst)
  exact ⟨hl, entryTime_of_not_tick hv hl h1 h2⟩

/-- Only critical services increase budgets. -/
theorem budget_succ_le_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) (e : ℤ) :
    (snapAt input (i + 1)).budget e ≤ (snapAt input i).budget e := by
  generalize hmv : moveAt i h = m at hm
  cases m with
  | tick t =>
    rw [(tick_spec hv h hmv).2.2.2.2]
  | advance t =>
    rw [(advance_spec hv h hmv).2.2.2.2.2.2]
  | critical p => exact absurd rfl (hm p)
  | skip e' =>
    rw [(skip_spec hv h hmv).2.2]
  | openHole e' =>
    obtain ⟨hst, -, hs⟩ := openHole_spec hv h hmv
    rw [hs]
    try simp only
    by_cases he : e = e'
    · subst he
      rw [Function.update_self]
      have : 0 ≤ holePayment input e :=
        mul_nonneg (levelWeight_pos e).le (by simp; linarith [Instance.delta_lt_one hv])
      linarith
    · rw [Function.update_of_ne he]
  | trip e' π =>
    obtain ⟨⟨b, hst⟩, -, -, hs⟩ := trip_spec hv h hmv
    rw [hs]
    try simp only
    by_cases he : e = e'
    · subst he
      rw [Function.update_self]
      linarith [(tripCost_nonneg_le hv hst π.page).1]
    · rw [Function.update_of_ne he]
  | closeHole e' stop =>
    obtain ⟨b, -, -, hs⟩ := closeHole_spec hv h hmv
    rw [hs]

theorem budget_succ_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    (snapAt input (i + 1)).budget e =
      if level input p ≤ e ∧ e ≤ maxLevel input then
        (snapAt input i).budget e + levelLen input (snapAt input i).x p e
      else (snapAt input i).budget e := by
  rw [(critical_spec hv h hm).2.2]
  rfl

theorem budget_succ_critical_ge {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    (snapAt input i).budget e ≤ (snapAt input (i + 1)).budget e := by
  rw [budget_succ_of_critical hv h hm]
  split_ifs
  · linarith [C.levelLen_nonneg (input := input) (snapAt input i).x p e]
  · exact le_rfl

end RunFacts

/-! ### Payments, deposits and the slack of a preemptive service -/

variable (input : Instance Page)

/-- The payment from `B_e` at entry `l` (the decrease of `B_e`, except at critical services). -/
def pay (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .critical _ => 0
    | _ => (snapAt input l).budget e - (snapAt input (l + 1)).budget e
  else 0

/-- The deposit into `B_e` at entry `l` (the increase of `B_e` at critical services). -/
def dep (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .critical _ => (snapAt input (l + 1)).budget e - (snapAt input l).budget e
    | _ => 0
  else 0

/-- The weight of the page of a level-`e` round trip at entry `l` (else `0`). -/
def tripWL (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .trip e' π => if e' = e then w π.page else 0
    | _ => 0
  else 0

/-- The slack of the preemptive service invariant: inside a level-`e` preemptive service, `B_e - 2^e`. -/
def slack (e : ℤ) (s : Snap Page) : ℝ :=
  match s.stage with
  | .preempt e' _ => if e' = e then s.budget e - levelWeight e else 0
  | _ => 0

variable {input}

theorem slack_of_not_preempt {s : Snap Page} {e : ℤ} (h : ∀ b, s.stage ≠ .preempt e b) :
    slack e s = 0 := by
  unfold slack
  rcases hs : s.stage with _ | e' | ⟨e', b⟩
  · rfl
  · rfl
  · simp only
    split_ifs with he
    · subst he; exact absurd hs (h b)
    · rfl

theorem slack_preempt {s : Snap Page} {e : ℤ} {b : Page → ℝ} (h : s.stage = .preempt e b) :
    slack e s = s.budget e - levelWeight e := by
  unfold slack
  rw [h]
  simp

theorem afterLevel_ne_preempt (e e' : ℤ) (b : Page → ℝ) :
    afterLevel input e ≠ .preempt e' b := by
  unfold afterLevel
  split_ifs <;> simp

/-- Telescoping inequality. -/
theorem sum_Ico_le_telescope (g u : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ l, a ≤ l → l < b → g l ≤ u (l + 1) - u l) :
    ∑ l ∈ Finset.Ico a b, g l ≤ u b - u a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have h1 := ih (fun l h1 h2 => h l h1 (by omega))
    have h2 := h n hn (by omega)
    linarith

theorem antitone_of_step (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ l, a ≤ l → l < b → f (l + 1) ≤ f l) : f b ≤ f a := by
  have := sum_Ico_le_telescope (fun _ => (0 : ℝ)) (fun l => - f l) hab
    (fun l h1 h2 => by have := h l h1 h2; simp; linarith)
  simp at this
  linarith

section

variable (hv : input.Valid)
include hv

theorem budget_step (e : ℤ) {l : ℕ} (hl : l < (log input).length) :
    dep input e l - pay input e l =
      (snapAt input (l + 1)).budget e - (snapAt input l).budget e := by
  unfold dep pay
  rw [dif_pos hl, dif_pos hl]
  cases moveAt l hl <;> simp

theorem dep_nonneg (e : ℤ) (l : ℕ) : 0 ≤ dep input e l := by
  unfold dep
  split_ifs with hl
  · generalize hmv : moveAt l hl = m
    cases m with
    | critical p =>
      try simp only
      linarith [budget_succ_critical_ge hv hl hmv e]
    | _ => simp
  · exact le_rfl

theorem dep_of_critical {e : ℤ} {l : ℕ} (hl : l < (log input).length) {p : Page}
    (hm : moveAt l hl = .critical p) (hle : level input p ≤ e)
    (he : e ≤ maxLevel input) :
    dep input e l = levelLen input (snapAt input l).x p e := by
  unfold dep
  rw [dif_pos hl, hm]
  try simp only
  rw [budget_succ_of_critical hv hl hm e, if_pos ⟨hle, he⟩]
  ring

/-- One step of the preemptive service invariant. -/
theorem slack_step (e : ℤ) {l : ℕ} (hl : l < (log input).length)
    (hno : moveAt l hl ≠ .closeHole e none) :
    slack e (snapAt input l) + (2 * pay input e l - 3 * tripWL input e l) ≤
      slack e (snapAt input (l + 1)) := by
  have hpay : ∀ m, moveAt l hl = m → pay input e l = (match m with
      | .critical _ => 0
      | _ => (snapAt input l).budget e - (snapAt input (l + 1)).budget e) := by
    intro m hm; unfold pay; rw [dif_pos hl, hm]
  have htw : ∀ m, moveAt l hl = m → tripWL input e l = (match m with
      | .trip e' π => if e' = e then w π.page else 0
      | _ => 0) := by
    intro m hm; unfold tripWL; rw [dif_pos hl, hm]
  generalize hmv : moveAt l hl = m at hno
  have hp := hpay m hmv
  have ht := htw m hmv
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, hs⟩ := tick_spec hv hl hmv
    try simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; simp [hst])]
    try simp only at hp
    rw [hp, ht]; simp
  | advance t =>
    obtain ⟨hst, -, -, -, -, -, hs⟩ := advance_spec hv hl hmv
    try simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; simp [hst])]
    try simp only at hp
    rw [hp, ht]; simp
  | critical p =>
    obtain ⟨hst, -, hs⟩ := critical_spec hv hl hmv
    try simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs, slack_of_not_preempt (by intro b; simp)]
    rw [hp, ht]; simp
  | skip e' =>
    obtain ⟨hst, -, hs⟩ := skip_spec hv hl hmv
    try simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; exact afterLevel_ne_preempt _ _ _)]
    try simp only at hp
    rw [hp, ht]; simp
  | openHole e' =>
    obtain ⟨hst, hcond, hs⟩ := openHole_spec hv hl hmv
    try simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    try simp only at hp
    rw [ht]
    by_cases he : e' = e
    · subst he
      rw [slack_preempt (by rfl)]
      simp only [Function.update_self] at hp ⊢
      have h1 : holePayment input e' ≤ (1 - δ) * levelWeight e' := by
        unfold holePayment; rw [mul_comm]
      have h2 := hcond.1
      have hd := Instance.delta_pos hv
      have hW := levelWeight_pos e'
      have h3 : (1 - δ) * levelWeight e' ≤ levelWeight e' := by nlinarith
      rw [hp]
      linarith
    · rw [slack_of_not_preempt (by intro b hb; simp at hb; exact he hb.1)]
      simp only [Function.update_of_ne (Ne.symm he)] at hp
      rw [hp]; simp
  | trip e' π =>
    obtain ⟨⟨b, hst⟩, hcand, hle, hs⟩ := trip_spec hv hl hmv
    try simp only at hp ht
    rw [hs] at hp ⊢
    try simp only at hp
    by_cases he : e' = e
    · subst he
      rw [slack_preempt hst, slack_preempt (by simpa using hst)]
      simp only [Function.update_self, if_pos] at hp ht ⊢
      have := (tripCost_nonneg_le hv hst π.page).2
      rw [hp, ht]
      linarith
    · rw [slack_of_not_preempt (by intro b' hb'; rw [hst] at hb'; simp at hb'; exact he hb'.1)]
      rw [slack_of_not_preempt (by intro b' hb'; simp [hst] at hb'; exact he hb'.1)]
      simp only [Function.update_of_ne (Ne.symm he), if_neg he] at hp ht
      rw [hp, ht]; simp
  | closeHole e' stop =>
    obtain ⟨b, hst, hstop, hs⟩ := closeHole_spec hv hl hmv
    try simp only at hp ht
    have h0 : slack e (snapAt input (l + 1)) = 0 :=
      slack_of_not_preempt (by intro b'; rw [hs]; exact afterLevel_ne_preempt _ _ _)
    rw [h0]
    rw [hs] at hp
    try simp only at hp
    rw [hp, ht]
    by_cases he : e' = e
    · subst he
      rw [slack_preempt hst]
      cases stop with
      | none => exact absurd rfl hno
      | some π =>
        simp; linarith [hstop.2]
    · rw [slack_of_not_preempt (by intro b' hb'; rw [hst] at hb'; simp at hb'; exact he hb'.1)]
      simp

/-- `lem:periodlevel`, the payments: between two idle entries, if no level-`e` preemptive service runs out of candidates, the payments from `B_e` are at most `3/2` times the weights of the level-`e` round trips. -/
theorem two_pay_le {e : ℤ} {i₀ i₁ : ℕ} (h01 : i₀ ≤ i₁) (h1 : i₁ ≤ (log input).length)
    (hst₀ : (snapAt input i₀).stage = .idle) (hst₁ : (snapAt input i₁).stage = .idle)
    (hno : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      moveAt l hl ≠ .closeHole e none) :
    2 * ∑ l ∈ Finset.Ico i₀ i₁, pay input e l ≤
      3 * ∑ l ∈ Finset.Ico i₀ i₁, tripWL input e l := by
  have := sum_Ico_le_telescope (fun l => 2 * pay input e l - 3 * tripWL input e l)
    (fun l => slack e (snapAt input l)) h01 (fun l hl1 hl2 => by
      have hl : l < (log input).length := by omega
      have := slack_step hv e hl (hno l hl hl1 hl2)
      (try simp only); linarith)
  try simp only at this
  rw [slack_of_not_preempt (by intro b; rw [hst₁]; simp),
    slack_of_not_preempt (by intro b; rw [hst₀]; simp)] at this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  linarith

/-- The deposits between two entries are at most the payments plus the final budget. -/
theorem sum_dep_le {e : ℤ} {i₀ i₁ : ℕ} (h01 : i₀ ≤ i₁) (h1 : i₁ ≤ (log input).length) :
    ∑ l ∈ Finset.Ico i₀ i₁, dep input e l ≤
      (snapAt input i₁).budget e + ∑ l ∈ Finset.Ico i₀ i₁, pay input e l := by
  have := sum_Ico_le_telescope (fun l => dep input e l - pay input e l)
    (fun l => (snapAt input l).budget e) h01 (fun l hl1 hl2 => by
      try simp only
      rw [budget_step hv e (by omega : l < (log input).length)])
  try simp only at this
  rw [Finset.sum_sub_distrib] at this
  have := budget_nonneg hv i₀ e
  linarith

/-- `lem:periodlevel`, the leftover budget: after a critical service on a page of level `≤ e`, the budget of level `e` is below `4 · 2^e` at the next such critical service (if no level-`e` preemptive service in between runs out of candidates). -/
theorem budget_lt_of_next_critical {e : ℤ} (he : e ≤ maxLevel input) {a b : ℕ}
    (hab : a < b) (hb : b < (log input).length) (ha : a < (log input).length) {p : Page}
    (hma : moveAt a ha = .critical p) (hp : level input p ≤ e)
    (hbp : ∃ p', moveAt b hb = .critical p')
    (hmid : ∀ l (hl : l < (log input).length), a < l → l < b →
      ∀ p', moveAt l hl = .critical p' → e < level input p')
    (hno : ∀ l (hl : l < (log input).length), a ≤ l → l < b →
      moveAt l hl ≠ .closeHole e none) :
    (snapAt input b).budget e < 4 * levelWeight e := by
  obtain ⟨j, hj, haj, hmj, hbet⟩ :=
    levelLoop_examines hv ha hma ((minLevel_le p).trans hp) he
  have hjb : j < b := by
    by_contra hcon
    obtain ⟨p', hp'⟩ := hbp
    exact (hbet b hb hab (by omega)).1 p' hp'
  have hW := levelWeight_pos e
  -- the budget right after the examination of level `e`
  have hj1 : (snapAt input (j + 1)).budget e < 4 * levelWeight e := by
    rcases hmj with hmj | ⟨stop, hmj⟩
    · obtain ⟨hst, hncond, hs⟩ := skip_spec hv hj hmj
      rw [hs]
      try simp only
      -- the hole condition holds, so the budget condition fails
      obtain ⟨-, -, hxa, hra, -⟩ := critical_facts hv ha hma
      have hbase : ∀ l, a + 1 ≤ l → l ≤ j →
          baseState (snapAt input l) = baseState (snapAt input (a + 1)) := by
        intro l h1 h2
        induction l, h1 using Nat.le_induction with
        | base => rfl
        | succ n hn ih =>
          rw [← ih (by omega)]
          exact baseState_succ_of_not_critical hv (by omega)
            (hbet n (by omega) (by omega) (by omega)).1
      have hxj : (snapAt input j).x = criticalState input (snapAt input a).x p := by
        rw [x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb),
          hbase j (by omega) le_rfl]
        have hs1 := (critical_spec hv ha hma).2.2
        have : (snapAt input (a + 1)).stage = .examine (minLevel input) := by rw [hs1]
        rw [← x_eq_baseState hv (by intro e b hb; rw [this] at hb; cases hb), hs1]
      have hrest := baseState_isRest hv j
      rw [← x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb)] at hrest
      have hcond : 1 - δ ≤
          ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e),
            (1 - (snapAt input j).x i) := by
        have hmem : p ∈ Finset.univ.filter (fun i => level input i ≤ e) := by simp [hp]
        have := Finset.single_le_sum (f := fun i => 1 - (snapAt input j).x i)
          (fun i _ => by have := (hrest.1 i).2; linarith) hmem
        try simp only at this
        rw [hxj, PagingWithDelay.PMD.criticalState_self hv hxa
          (by simpa using hra)] at this
        rw [hxj]
        exact this
      unfold preemptCondition at hncond
      push_neg at hncond
      by_contra hcon
      push_neg at hcon
      exact absurd hcond (not_le.2 (hncond hcon))
    · obtain ⟨bb, hst, hstop, hs⟩ := closeHole_spec hv hj hmj
      rw [hs]
      try simp only
      cases stop with
      | none => exact absurd hmj (hno j hj (by omega) hjb)
      | some π =>
        linarith [hstop.2]
  -- afterwards it does not increase until `b`
  have hmono := antitone_of_step (fun l => (snapAt input l).budget e) (show j + 1 ≤ b by omega)
    (fun l h1 h2 => by
      have hl : l < (log input).length := by omega
      try simp only
      generalize hmv : moveAt l hl = m
      cases m with
      | critical p' =>
        rw [budget_succ_of_critical hv hl hmv e,
          if_neg (fun h => absurd h.1 (not_le.2 (hmid l hl (by omega) h2 p' hmv)))]
      | _ => exact budget_succ_le_of_not_critical hv hl (by intro p' h; rw [hmv] at h; cases h) e)
  try simp only at hmono
  linarith

end

end

end ExcessProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.PeriodLevel` -/
section

/-!
# The early part, one period and one level (`lem:early`, `lem:periodlevel`)

Fix a step time `τ` of the comparator (the start `t_j` of period `j`) and a level `e` whose weight `W = 2^e` is below every weight in the comparator's cache `O_j`. The *light services* `λ^(1), …, λ^(m)` are the overdue critical services of the period on pages of level `≤ e` (`lightServices`). The *early part* consists of the entries of the period before `λ^(m)`.

`lem:early` (`early_spec`): at `λ^(m)` (time `t_m`) some page `q` with `w_q ≤ w_{p_m} ≤ W` is overdue, so the comparator has served some pending request `r` on `q` by `t_m`. As `q` is not cached in the period, `r` was served by `τ`, so `a_r ≤ τ` and `r` is pending at every level-`e` preemptive service of the early part. Hence these never run out of candidates and stop for lack of budget (`B_W < W`). The pending requests on `q` have delay `> w_q` at `t_m`, so the deadline of `q`, and thus of every page chosen for a round trip, is at most `t_m`. A round trip on `p` is then chargeable: either the comparator has served a pending request on `p` (so `p` is not cached), or it has served none by `t_m` and pays at least their delay at `t_m`, which is at least `w_p`.

`lem:periodlevel` (`periodLevel_sum`): the deposits `|λ^(ℓ)|_W` of the light services of one period and one level are at most `4W + (3/2) C_{j,W} + L W`, where `C_{j,W}` is the total weight of the chargeable level-`e` round trips of the period.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

namespace ExcessProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost afterLevel Stage IsRest IsFrac levelWeight_pos
  minLevel_le)
open PagingWithDelay.Schedule (cacheAt ServedBy stepTimes)
open PagingWithDelay.Schedule (InPer)

open Classical

noncomputable section

/-! ### Definitions -/

variable (input : Instance Page)

/-- The length `|λ|_W` in level `e` of the critical service at entry `i` (else `0`). -/
def levelLenAt (i : ℕ) (e : ℤ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => levelLen input (snapAt input i).x p e
    | _ => 0
  else 0

/-- Entry `i` is a critical service on a page of level `≤ e`. -/
def IsLightService (e : ℤ) (i : ℕ) : Prop :=
  ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧ level input p ≤ e

variable (σ : Request Page → ℝ) (S : Schedule Page)

/-- The *light services* of the period of `τ` and the level `e`: the overdue critical services of the period on pages of level `≤ e`. -/
def lightServices (τ : ℝ) (e : ℤ) : Finset ℕ :=
  (Finset.range (log input).length).filter
    (fun i => IsLightService input e i ∧ IsOverdue input σ S i ∧ InPer S τ (entryTime input i))

/-- The level-`e` round trips of the period of `τ`. -/
def periodTrips (τ : ℝ) (e : ℤ) : Finset ℕ :=
  (Finset.range (log input).length).filter
    (fun l => (∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) ∧
      InPer S τ (entryTime input l))

variable {input σ S}

/-! ### Small facts -/

theorem levelLenAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    levelLenAt input i e = levelLen input (snapAt input i).x p e := by
  unfold levelLenAt
  rw [dif_pos h, hm]

theorem levelLenAt_nonneg (i : ℕ) (e : ℤ) : 0 ≤ levelLenAt input i e := by
  unfold levelLenAt
  split_ifs with h
  · split
    · exact C.levelLen_nonneg _ _ _
    · exact le_rfl
  · exact le_rfl

theorem levelLenAt_le (i : ℕ) (e : ℤ) : levelLenAt input i e ≤ L * levelWeight e := by
  have hL := L_nonneg' input
  have hW := levelWeight_pos e
  unfold levelLenAt
  split_ifs with h
  · split
    · exact levelLen_le _ _ _
    · positivity
  · positivity

theorem visitPage_of_trip {l : ℕ} (h : l < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt l h = .trip e π) : visitPage input l = some π.page := by
  unfold visitPage
  rw [dif_pos h, hm]

theorem chargeW_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ chargeW input σ S l := by
  unfold chargeW
  split_ifs
  · split
    · exact (hv.weight_pos _).le
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ tripChargeW input σ S l := by
  unfold tripChargeW
  split_ifs with h
  · split
    · exact chargeW_nonneg hv l
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_of_chargeable {l : ℕ} (h : l < (log input).length) {e : ℤ}
    {π : Request Page} (hm : moveAt l h = .trip e π) (hc : IsChargeable input σ S l) :
    tripChargeW input σ S l = w π.page := by
  unfold tripChargeW chargeW
  rw [dif_pos h, hm]
  try simp only
  rw [if_pos hc, visitPage_of_trip h hm]

theorem tripWL_eq_zero {l : ℕ} {e : ℤ}
    (hno : ¬ ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) :
    tripWL input e l = 0 := by
  unfold tripWL
  split_ifs with h
  · generalize hmv : moveAt l h = m
    cases m with
    | trip e' π =>
      try simp only
      split_ifs with he
      · subst he; exact absurd ⟨h, π, hmv⟩ hno
      · rfl
    | _ => rfl
  · rfl

theorem tripWL_of_trip {l : ℕ} (h : l < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt l h = .trip e π) : tripWL input e l = w π.page := by
  unfold tripWL
  rw [dif_pos h, hm]
  simp

theorem servedBy_mono {ρ : Request Page} {t t' : ℝ} (htt' : t ≤ t')
    (h : ServedBy input σ S ρ t) :
    ServedBy input σ S ρ t' := by
  obtain ⟨s, h1, h2, h3, h4⟩ := h
  exact ⟨s, h1, h2, h3.trans htt', h4⟩

/-- An overdue page has a pending request that the comparator has served. -/
theorem exists_served_of_overdue (hv : input.Valid) {s : Snap Page} {q : Page} {t : ℝ}
    (h : PageOverdue input σ S s q t) :
    ∃ r ∈ s.pending, r.page = q ∧ ServedBy input σ S r t := by
  by_contra hcon
  push_neg at hcon
  have hnil : (s.pending.filter fun ρ => decide (ρ.page = q ∧
      ServedBy input σ S ρ t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp only [decide_eq_true_eq, not_and]
    exact hcon r hr
  unfold PageOverdue servedDelay at h
  rw [hnil] at h
  simp at h
  linarith [hv.weight_pos q]

/-! ### Deadlines of pages -/

theorem pageDeadline_le {pending : List (Request Page)} {t T : ℝ} {p : Page} (htT : t ≤ T)
    (h : w p < pageDelay pending p T) : pageDeadline input pending t p ≤ T :=
  csInf_le ⟨t, fun x hx => hx.1⟩ ⟨htT, h⟩

/-- If the deadline of `p` is at most `T`, the delay of the pending requests on `p` at `T` is at least `w_p` (the delays are continuous). -/
theorem weight_le_pageDelay {pending : List (Request Page)} {t T : ℝ} {p : Page}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hcont : ∀ ρ ∈ pending, Continuous ρ.delay)
    (hne : ∃ x, t ≤ x ∧ w p < pageDelay pending p x)
    (h : pageDeadline input pending t p ≤ T) : w p ≤ pageDelay pending p T := by
  set A := {x | t ≤ x ∧ w p < pageDelay pending p x} with hA
  have hB : IsClosed {x | w p ≤ pageDelay pending p x} :=
    isClosed_le continuous_const (continuous_pageDelay hcont p)
  have hAB : A ⊆ {x | w p ≤ pageDelay pending p x} := fun x hx => hx.2.le
  have hmem := closure_minimal hAB hB (csInf_mem_closure hne ⟨t, fun x hx => hx.1⟩)
  exact hmem.trans (pageDelay_mono hmono p h)

/-- A page with a pending request has a deadline: the delay of its pending requests eventually exceeds `w_p`. -/
theorem exists_pageDelay_gt {pending : List (Request Page)} {t : ℝ} {p : Page}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ pending, ρ.delay 0 = 0)
    (hunb : ∀ ρ ∈ pending, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ)
    (harr : ∀ ρ ∈ pending, ρ.arrival ≤ t) {π : Request Page} (hπ : π ∈ pending)
    (hπp : π.page = p) : ∃ x, t ≤ x ∧ w p < pageDelay pending p x := by
  obtain ⟨τ₀, hτ₀⟩ := hunb π hπ (w p + 1)
  refine ⟨max t (τ₀ + π.arrival), le_max_left _ _, ?_⟩
  have h1 := delay_le_pageDelay hmono hzero
    (fun ρ hρ => (harr ρ hρ).trans (le_max_left t (τ₀ + π.arrival))) hπ
  rw [hπp] at h1
  have h2 : π.delay τ₀ ≤ π.delay (max t (τ₀ + π.arrival) - π.arrival) :=
    hmono π hπ (by linarith [le_max_right t (τ₀ + π.arrival)])
  linarith

/-! ### The pending list shrinks, apart from new arrivals -/

section Pending

variable (hv : input.Valid)
include hv

/-- One move: the pending requests satisfying `P` (which have arrived by `T`) form a sublist of the earlier ones, unless the move is a tick at a time `≤ T`. -/
theorem pending_filter_sublist_succ {m : ℕ} (T : ℝ) (P : Request Page → Bool)
    (hP : ∀ ρ, P ρ = true → ρ.arrival ≤ T)
    (htick : ∀ (hm : m < (log input).length) t, moveAt m hm = .tick t → T < t) :
    ((snapAt input (m + 1)).pending.filter P).Sublist ((snapAt input m).pending.filter P) := by
  by_cases hm : m < (log input).length
  · generalize hmv : moveAt m hm = mv
    cases mv with
    | tick t =>
      obtain ⟨-, -, -, -, hs⟩ := tick_spec hv hm hmv
      rw [hs]
      try simp only
      rw [List.filter_append, List.filter_append]
      have hnil : ((input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          (fun ρ => decide ((snapAt input m).x ρ.page ≠ δ))).filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro ρ hρ hPρ
        simp only [List.mem_filter, decide_eq_true_eq] at hρ
        have := hP ρ hPρ
        have := htick hm t hmv
        linarith [hρ.1.2]
      rw [hnil, List.append_nil]
      exact List.filter_sublist.filter P
    | critical p =>
      obtain ⟨-, -, hs⟩ := critical_spec hv hm hmv
      rw [hs]
      exact List.filter_sublist.filter P
    | trip e π =>
      obtain ⟨-, -, -, hs⟩ := trip_spec hv hm hmv
      rw [hs]
      exact List.filter_sublist.filter P
    | _ =>
      rw [pending_succ_of_not_visit hv hm (by intro p h; rw [hmv] at h; cases h)
        (by intro e π h; rw [hmv] at h; cases h) (by intro t h; rw [hmv] at h; cases h)]
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

theorem pending_filter_sublist {l j : ℕ} (hlj : l ≤ j) (T : ℝ) (P : Request Page → Bool)
    (hP : ∀ ρ, P ρ = true → ρ.arrival ≤ T)
    (htick : ∀ m (hm : m < (log input).length), l ≤ m → m < j → ∀ t,
      moveAt m hm = .tick t → T < t) :
    ((snapAt input j).pending.filter P).Sublist ((snapAt input l).pending.filter P) := by
  induction j, hlj using Nat.le_induction with
  | base => exact List.Sublist.refl _
  | succ n hn ih =>
    exact (pending_filter_sublist_succ hv T P hP (fun hm t h => htick n hm hn (by omega) t h)).trans
      (ih (fun m hm h1 h2 t h => htick m hm h1 (by omega) t h))

/-- Ticks after entry `l > 0` happen after the time `(snapAt l).now`. -/
theorem lt_of_tick_after {l m : ℕ} (hl0 : 0 < l) (hlm : l ≤ m) (hm : m < (log input).length)
    {t : ℝ} (hmt : moveAt m hm = .tick t) : (snapAt input l).now < t := by
  have := entryTime_lt_of_tick hv hm hmt (j := l - 1) (by omega)
  unfold entryTime at this
  rwa [Nat.sub_add_cancel hl0] at this

end Pending

/-! ### `lem:early` -/

section Early

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hSw : Schedule.SwapForm input S)
  (hF : S.FeasibleBy input σ)
  {τ : ℝ} {e : ℤ}
  (hW : ∀ q ∈ cacheAt input S τ, levelWeight e < w q)

section Comparator

include hv hW in
theorem not_mem_cacheAt {p : Page} (hp : level input p ≤ e) :
    p ∉ cacheAt input S τ :=
  fun hmem => absurd (hW p hmem) (not_lt.2 ((level_le_iff' hv p e).1 hp))

include hSw in
/-- `obs:servedbefore`: a request on a page not cached in the period of `τ` that the comparator has served by a time `T` of the period was served by `τ`. -/
theorem servedBy_start {T : ℝ} (hper : InPer S τ T) {ρ : Request Page}
    (hp : ρ.page ∉ cacheAt input S τ)
    (hs : ServedBy input σ S ρ T) :
    ServedBy input σ S ρ τ := by
  have hc := hSw.chronological
  obtain ⟨s, h1, h2, h3, h4⟩ := hs
  by_cases hsτ : s ≤ τ
  · exact ⟨s, h1, h2, hsτ, h4⟩
  exfalso
  have hτs : τ < s := not_le.1 hsτ
  obtain ⟨st, hst, hstτ⟩ := Schedule.mem_stepTimes.1 hper.1
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hst
  rcases h4 with ⟨-, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
  · have := Schedule.head_le hc hh hi
    linarith
  · have hjτ : S[j].time ≤ τ := by
      by_contra hcon
      exact hper.2.2 _ (List.getElem_mem hj) ⟨not_le.1 hcon, ha.trans h3⟩
    apply hp
    rw [Schedule.cacheAt_eq_of_last hc hj hjτ
      (fun st hst => lt_of_lt_of_le hτs (hb st hst))]
    exact hpj

end Comparator

include hv hσ hSw hF hW

/-- `lem:early`: let `i'` be a light service of the period of `τ` and level `e`, and `l < i'` an entry of the period. If `l` is a level-`e` round trip, it is chargeable; if `l` closes a level-`e` hole, the preemptive service stopped for lack of budget, ending with `B_W < W`. -/
theorem early_spec {l i' : ℕ} (hl : l < (log input).length)
    (hper : InPer S τ (entryTime input l)) (hi' : i' ∈ lightServices input σ S τ e)
    (hli' : l < i') :
    (∀ π, moveAt l hl = .trip e π → IsChargeable input σ S l) ∧
    (∀ stop, moveAt l hl = .closeHole e stop →
      stop ≠ none ∧ (snapAt input (l + 1)).budget e < levelWeight e) := by
  have hvb := hv
  -- the light service `i'` and its overdue page `q`
  simp only [lightServices, Finset.mem_filter, Finset.mem_range] at hi'
  obtain ⟨-, ⟨h', p', hm', hle'⟩, ⟨h'', p'', hm'', q, hwq, hov⟩, hper'⟩ := hi'
  have hpp : p'' = p' := by
    have := hm''.symm.trans hm'
    cases this; rfl
  subst hpp
  have hlq : level input q ≤ e :=
    (level_le_iff' hv q e).2 (hwq.trans ((level_le_iff' hv p'' e).1 hle'))
  have hqc := not_mem_cacheAt hv hW hlq
  set t' := entryTime input i' with ht'
  have ht'now : t' = (snapAt input i').now := (critical_facts hv h' hm').2.2.2.2
  obtain ⟨r, hr, hrq, hrs⟩ := exists_served_of_overdue hv hov
  -- the requests on `q` served by `t'` were served by `τ`, so they arrived by `τ`
  have hservedτ : ∀ ρ : Request Page, ρ.page = q →
      ServedBy input σ S ρ t' → ρ.arrival ≤ τ := by
    intro ρ hρq hρs
    have hρc : ρ.page ∉ cacheAt input S τ := hρq ▸ hqc
    obtain ⟨s, h1, -, h3, -⟩ := servedBy_start hSw hper' hρc hρs
    exact h1.trans h3
  -- the facts at entry `l`, which is inside a level-`e` preemptive service
  have hcommon : ∀ b, (snapAt input l).stage = .preempt e b →
      0 < l ∧ entryTime input l = (snapAt input l).now ∧ r ∈ (snapAt input l).pending := by
    intro b hst
    have hl0 : 0 < l := by
      rcases Nat.eq_zero_or_pos l with rfl | h
      · rw [snapAt_zero hv] at hst; simp [initialSnap] at hst
      · exact h
    obtain ⟨-, hlt⟩ := entryTime_of_preempt hv hst
    refine ⟨hl0, hlt, ?_⟩
    have := pending_of_later hv (show l - 1 < i' by omega) hr
      ((hservedτ r hrq hrs).trans (by
        unfold entryTime; rw [Nat.sub_add_cancel hl0, ← hlt]; exact hper.2.1))
    rwa [Nat.sub_add_cancel hl0] at this
  have hrl : level input r.page ≤ e := hrq ▸ hlq
  constructor
  · intro π hm
    obtain ⟨⟨b, hst⟩, hcand, -, -⟩ := trip_spec hv hl hm
    obtain ⟨hl0, hlt, hrP⟩ := hcommon b hst
    set P := (snapAt input l).pending with hPdef
    set t := (snapAt input l).now with htdef
    have htt' : t ≤ t' := by rw [← hlt]; exact entryTime_mono hv hli'.le
    -- facts on the pending requests at `l`
    have hPreq : ∀ ρ ∈ P, ρ ∈ input.requests := fun ρ hρ => (pending_spec hv hρ).1
    have hParr : ∀ ρ ∈ P, ρ.arrival ≤ t := fun ρ hρ => (pending_spec hv hρ).2.1
    have hmono : ∀ ρ ∈ P, Monotone ρ.delay := fun ρ hρ => hv.delay_mono ρ (hPreq ρ hρ)
    have hzero : ∀ ρ ∈ P, ρ.delay 0 = 0 := fun ρ hρ => hv.delay_zero ρ (hPreq ρ hρ)
    have hcont : ∀ ρ ∈ P, Continuous ρ.delay := fun ρ hρ => hv.delay_continuous ρ (hPreq ρ hρ)
    have hunb : ∀ ρ ∈ P, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ :=
      fun ρ hρ => hv.delay_unbounded ρ (hPreq ρ hρ)
    -- the delay at `t'` of the pending requests on `q` exceeds `w_q`
    have hqdelay : w q < pageDelay P q t' := by
      have hov' : w q < servedDelay input σ S (snapAt input i') q t' := hov
      refine hov'.trans_le ?_
      unfold servedDelay pageDelay
      set Q : Request Page → Bool := fun ρ => decide (ρ.page = q ∧ ρ.arrival ≤ τ) with hQ
      have hs1 : ((snapAt input i').pending.filter fun ρ => decide (ρ.page = q ∧
          ServedBy input σ S ρ t')).Sublist
          ((snapAt input i').pending.filter Q) := by
        apply List.monotone_filter_right
        intro ρ hρ
        simp only [decide_eq_true_eq, hQ] at hρ ⊢
        exact ⟨hρ.1, hservedτ ρ hρ.1 hρ.2⟩
      have hs2 : ((snapAt input i').pending.filter Q).Sublist (P.filter Q) := by
        apply pending_filter_sublist hv hli'.le τ Q
        · intro ρ hρ; simp only [decide_eq_true_eq, hQ] at hρ; exact hρ.2
        · intro m hm h1 h2 t₀ hmt
          exact lt_of_le_of_lt (le_of_le_of_eq hper.2.1 hlt)
            (lt_of_tick_after hv hl0 h1 hm hmt)
      have hs3 : (P.filter Q).Sublist (P.filter fun ρ => decide (ρ.page = q)) := by
        apply List.monotone_filter_right
        intro ρ hρ
        simp only [decide_eq_true_eq, hQ] at hρ ⊢
        exact hρ.1
      apply List.Sublist.sum_le_sum (((hs1.trans hs2).trans hs3).map _)
      intro a ha
      simp only [List.mem_map, List.mem_filter] at ha
      obtain ⟨ρ, ⟨hρ, -⟩, rfl⟩ := ha
      rw [← hzero ρ hρ]
      exact hmono ρ hρ (by linarith [hParr ρ hρ])
    have hdq : pageDeadline input P t q ≤ t' := pageDeadline_le htt' hqdelay
    -- the trip is chosen over `r`, so the deadline of its page is at most `t'`
    obtain ⟨hπ, hπle, hπd⟩ := tripCandidate_spec hcand
    have hdπ : pageDeadline input P t π.page ≤ t' :=
      (hπd r hrP hrl).trans (by rw [hrq]; exact hdq)
    have hwπ : w π.page ≤ pageDelay P π.page t' :=
      weight_le_pageDelay hmono hcont
        (exists_pageDelay_gt hmono hzero hunb hParr hπ rfl) hdπ
    have hπc : π.page ∉ cacheAt input S (entryTime input l) := by
      rw [Schedule.InPer.cacheAt_eq hv hSw hper]; exact not_mem_cacheAt hv hW hπle
    refine ⟨π.page, visitPage_of_trip hl hm, ?_⟩
    by_cases hserved : ∃ ρ ∈ P, ρ.page = π.page ∧
        ServedBy input σ S ρ (entryTime input l)
    · exact Or.inl ⟨hπc, hserved⟩
    · right
      push_neg at hserved
      -- no pending request on `π.page` is served by `t'`
      have hns : ∀ ρ ∈ P, ρ.page = π.page →
          ¬ ServedBy input σ S ρ t' := by
        intro ρ hρ hρp hs
        have hρc : ρ.page ∉ cacheAt input S τ :=
          hρp ▸ not_mem_cacheAt hv hW hπle
        exact hserved ρ hρ hρp (servedBy_mono hper.2.1 (servedBy_start hSw hper' hρc hs))
      refine hwπ.trans ((PendingProof.pageDelay_le_sum hv l π.page t'
        (fun ρ hρ => (hParr ρ hρ).trans htt')).trans ?_)
      unfold optDelayOn
      apply Finset.sum_le_sum
      intro j hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Schedule.delay_le_of_not_servedBy' hF hv j (hns _ hk.1 hk.2)
  · intro stop hm
    obtain ⟨b, hst, hstop, hs⟩ := closeHole_spec hv hl hm
    obtain ⟨-, -, hrP⟩ := hcommon b hst
    cases stop with
    | none => exact absurd hstop (tripCandidate_ne_none hrP hrl)
    | some π =>
      rw [hs]
      exact ⟨Option.some_ne_none π, hstop.2⟩

omit hσ hSw hF hW in
theorem stage_idle_of_mem {i : ℕ} (hi : i ∈ lightServices input σ S τ e) :
    ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧ level input p ≤ e ∧
      (snapAt input i).stage = .idle ∧ InPer S τ (entryTime input i) := by
  simp only [lightServices, Finset.mem_filter] at hi
  obtain ⟨-, ⟨h, p, hm, hle⟩, -, hper⟩ := hi
  exact ⟨h, p, hm, hle, (critical_spec hv h hm).1, hper⟩

/-- `lem:periodlevel`: the deposits of the light services of one period and one level are at most `4W + (3/2) C_{j,W} + L W`, where `C_{j,W}` is the total weight of the chargeable level-`e` round trips of the period. The deposit of `λ^(m)` is at most `L W`; those of `λ^(1), …, λ^(m-1)` are at most the payments from `B_W` between `λ^(1)` and `λ^(m)` plus the budget left at `λ^(m)`. -/
theorem periodLevel_sum (he : e ≤ maxLevel input) :
    ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e ≤
      4 * levelWeight e + 3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l +
        L * levelWeight e := by
  set Φ := lightServices input σ S τ e with hΦ
  set T := ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun l _ => tripChargeW_nonneg hv l
  have hW0 := levelWeight_pos e
  have hL := L_nonneg' input
  have hR0 : 0 ≤ 4 * levelWeight e + 3 / 2 * T := by positivity
  rcases Φ.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty]; nlinarith
  -- the last light service `λ^(m)`; its term is at most `L W`
  set i₁ := Φ.max' hne with hi₁def
  have hi₁ : i₁ ∈ Φ := Finset.max'_mem _ _
  rw [← Finset.add_sum_erase Φ _ hi₁]
  have hfirst : levelLenAt input i₁ e ≤ L * levelWeight e := levelLenAt_le _ _
  suffices hrest : ∑ i ∈ Φ.erase i₁, levelLenAt input i e ≤
      4 * levelWeight e + 3 / 2 * T by linarith
  rcases (Φ.erase i₁).eq_empty_or_nonempty with hemp' | hne'
  · rw [hemp', Finset.sum_empty]; exact hR0
  -- the first light service `λ^(1)`
  set i₀ := (Φ.erase i₁).min' hne' with hi₀def
  have hi₀ : i₀ ∈ Φ.erase i₁ := Finset.min'_mem _ _
  have hlt_of : ∀ x ∈ Φ.erase i₁, x < i₁ := fun x hx =>
    lt_of_le_of_ne (Finset.le_max' Φ x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hi₀lt := hlt_of i₀ hi₀
  obtain ⟨h₁, p₁, hm₁, -, hst₁, hper₁⟩ := stage_idle_of_mem hv hi₁
  obtain ⟨h₀, p₀, hm₀, hle₀, hst₀, hper₀⟩ :=
    stage_idle_of_mem hv (Finset.mem_of_mem_erase hi₀)
  -- the entries from `λ^(1)` up to `λ^(m)` lie in the early part
  have hperl : ∀ l, i₀ ≤ l → l ≤ i₁ → InPer S τ (entryTime input l) := fun l h1 h2 =>
    hper₁.of_le (hper₀.2.1.trans (entryTime_mono hv h1)) (entryTime_mono hv h2)
  have hearly : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      (∀ π, moveAt l hl = .trip e π → IsChargeable input σ S l) ∧
      (∀ stop, moveAt l hl = .closeHole e stop →
        stop ≠ none ∧ (snapAt input (l + 1)).budget e < levelWeight e) :=
    fun l hl h1 h2 => early_spec hv hσ hSw hF hW hl (hperl l h1 h2.le) hi₁ h2
  have hno : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      moveAt l hl ≠ .closeHole e none := fun l hl h1 h2 hmv =>
    ((hearly l hl h1 h2).2 none hmv).1 rfl
  -- the last critical service of level `≤ e` before `λ^(m)`
  set Cr := (Finset.Ico i₀ i₁).filter (fun l => IsLightService input e l) with hCr
  have hCrne : Cr.Nonempty := ⟨i₀, Finset.mem_filter.2
    ⟨Finset.mem_Ico.2 ⟨le_rfl, hi₀lt⟩, ⟨h₀, p₀, hm₀, hle₀⟩⟩⟩
  set a := Cr.max' hCrne with hadef
  have ha : a ∈ Cr := Finset.max'_mem _ _
  obtain ⟨haI, ⟨ha', pa, hma, hlea⟩⟩ := Finset.mem_filter.1 ha
  obtain ⟨hi₀a, hai₁⟩ := Finset.mem_Ico.1 haI
  -- the budget of level `e` between `λ^(1)` and `λ^(m)`
  have hpay := two_pay_le hv hi₀lt.le h₁.le hst₀ hst₁ hno
  have hdep := sum_dep_le hv (e := e) hi₀lt.le h₁.le
  have hmid : ∀ l (hl : l < (log input).length), a < l → l < i₁ →
      ∀ p', moveAt l hl = .critical p' → e < level input p' := by
    intro l hl h1 h2 p' hm
    by_contra hcon
    push_neg at hcon
    have hlC : l ∈ Cr := Finset.mem_filter.2
      ⟨Finset.mem_Ico.2 ⟨by omega, h2⟩, ⟨hl, p', hm, hcon⟩⟩
    have : l ≤ a := Finset.le_max' Cr l hlC
    omega
  -- the budget left at the end of the early part is below `4W`
  have hbal := budget_lt_of_next_critical hv he hai₁ h₁ ha' hma hlea ⟨p₁, hm₁⟩ hmid
    (fun l hl h1 h2 => hno l hl (by omega) h2)
  -- deposits of the light services before `λ^(m)`
  have hdepΦ : ∑ i ∈ Φ.erase i₁, levelLenAt input i e ≤
      ∑ l ∈ Finset.Ico i₀ i₁, dep input e l := by
    calc ∑ i ∈ Φ.erase i₁, levelLenAt input i e
        = ∑ i ∈ Φ.erase i₁, dep input e i := by
          apply Finset.sum_congr rfl
          intro i hi
          obtain ⟨h, p, hm, hle, -, -⟩ :=
            stage_idle_of_mem hv (Finset.mem_of_mem_erase hi)
          rw [levelLenAt_of_critical h hm, dep_of_critical hv h hm hle he]
      _ ≤ ∑ l ∈ Finset.Ico i₀ i₁, dep input e l := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_Ico.2 ⟨Finset.min'_le _ _ hx, hlt_of x hx⟩
          · intro x _ _; exact dep_nonneg hv e x
  -- the level-`e` round trips there are chargeable (`lem:early`)
  have htrip : ∑ l ∈ Finset.Ico i₀ i₁, tripWL input e l ≤ T := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico i₀ i₁)
      (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π)]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun l => ¬ _) _)
      (fun l hl => tripWL_eq_zero (Finset.mem_filter.1 hl).2), add_zero]
    calc ∑ l ∈ (Finset.Ico i₀ i₁).filter
          (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π),
          tripWL input e l
        = ∑ l ∈ (Finset.Ico i₀ i₁).filter
          (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π),
          tripChargeW input σ S l := by
          apply Finset.sum_congr rfl
          intro l hl
          obtain ⟨hlI, h, π, hm⟩ := Finset.mem_filter.1 hl
          obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hlI
          rw [tripWL_of_trip h hm,
            tripChargeW_of_chargeable h hm ((hearly l h h1 h2).1 π hm)]
      _ ≤ T := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro l hl
            obtain ⟨hlI, h, π, hm⟩ := Finset.mem_filter.1 hl
            obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hlI
            simp only [periodTrips, Finset.mem_filter, Finset.mem_range]
            exact ⟨h, ⟨h, π, hm⟩, hperl l h1 h2.le⟩
          · intro l _ _; exact tripChargeW_nonneg hv l
  linarith

end Early

end

end ExcessProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.Excess` -/
section

/-!
# The excess of overdue services (`prop:excess`, overdue part)

The excess of an overdue miss service `λ` on `p` in the period of `τ` is the sum of its deposits `|λ|_W` over the levels `w_p ≤ W < w_min(O_j)`, at each of which `λ` is a light service. Regrouping by periods and levels, `lem:periodlevel` bounds each group by `(L + 4) W + (3/2) C_{j,W}`; the chargeable round trips of distinct groups are distinct entries, and `∑_j ∑_{W < w_min(O_j)} W ≤ ∑_j w_min(O_j)` is at most the comparator's fetch cost (`lem:lightest`).

No overdue service with positive excess happens before the comparator's first step: its overdue page `q` (with `w_q ≤ w_p ≤ W < w_min(C₀)`) has a pending request served by the comparator while only `C₀` was cached, but `q ∉ C₀`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

namespace ExcessProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight levelWeight_pos minLevel_le)
open PagingWithDelay.Schedule (cacheAt ServedBy stepTimes)
open PagingWithDelay.Schedule (InPer)

open Classical

noncomputable section

/-- The levels whose weight is below every weight cached at `τ`. -/
def lightLevels (input : Instance Page) (S : Schedule Page) (τ : ℝ) :
    Finset ℤ :=
  (Finset.Icc (minLevel input) (maxLevel input)).filter
    (fun e => ∀ q ∈ cacheAt input S τ, levelWeight e < w q)

/-- Distinct powers of two below `2^b` sum to less than `2^b`. -/
theorem sum_levelWeight_lt (s : Finset ℤ) :
    ∀ b : ℤ, (∀ e ∈ s, e < b) → ∑ e ∈ s, levelWeight e < levelWeight b := by
  induction s using Finset.induction_on_max with
  | empty => intro b _; simpa using levelWeight_pos b
  | insert a s ha ih =>
    intro b hb
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have h1 := ih a ha
    have hab : a + 1 ≤ b := hb a (Finset.mem_insert_self a s)
    have h2 : levelWeight (a + 1) ≤ levelWeight b := by
      unfold levelWeight
      exact zpow_le_zpow_right₀ (by norm_num) hab
    rw [PagingWithDelay.PMD.levelWeight_succ] at h2
    linarith

theorem lt_of_levelWeight_lt {e b : ℤ} (h : levelWeight e < levelWeight b) : e < b := by
  by_contra hcon
  push_neg at hcon
  have : levelWeight b ≤ levelWeight e := by
    unfold levelWeight
    exact zpow_le_zpow_right₀ (by norm_num) hcon
  linarith

variable {input : Instance Page} {σ : Request Page → ℝ} {S : Schedule Page}

theorem isLightService_iff {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    IsLightService input e i ↔ level input p ≤ e := by
  constructor
  · rintro ⟨h', p', hm', hle⟩
    have := hm.symm.trans hm'
    cases this
    exact hle
  · intro hle
    exact ⟨h, p, hm, hle⟩

/-- The chargeable level-`e` round trips of the periods and levels are distinct entries: their total weight is at most `∑_l tripChargeW l`. -/
theorem sum_periodTrips_le (hv : input.Valid) :
    ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
        ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l ≤
      ∑ l ∈ Finset.range (log input).length, tripChargeW input σ S l := by
  set N := (log input).length
  set f := fun l => tripChargeW input σ S l with hf
  set cond : ℝ → ℤ → ℕ → Prop := fun τ e l =>
    (∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) ∧
      InPer S τ (entryTime input l) with hcond
  have hrw : ∀ τ e, ∑ l ∈ periodTrips input S τ e, f l =
      ∑ l ∈ Finset.range N, if cond τ e l then f l else 0 := by
    intro τ e
    unfold periodTrips
    rw [Finset.sum_filter]
  simp only [hrw]
  -- swap the sums over the levels and the entries
  have hsw : ∀ τ, ∑ e ∈ lightLevels input S τ, ∑ l ∈ Finset.range N,
      (if cond τ e l then f l else 0) =
      ∑ l ∈ Finset.range N, ∑ e ∈ lightLevels input S τ,
        (if cond τ e l then f l else 0) := fun τ => Finset.sum_comm
  simp only [hsw]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro l _
  by_cases hex : ∃ τ₀ ∈ stepTimes S, ∃ e₀ ∈ lightLevels input S τ₀, cond τ₀ e₀ l
  · obtain ⟨τ₀, hτ₀, e₀, he₀, hc₀⟩ := hex
    rw [Finset.sum_eq_single τ₀]
    · rw [Finset.sum_eq_single e₀]
      · rw [if_pos hc₀]
      · intro e _ hne
        rw [if_neg]
        rintro ⟨⟨h, π, hm⟩, -⟩
        obtain ⟨⟨h', π', hm'⟩, -⟩ := hc₀
        have := hm.symm.trans hm'
        cases this
        exact hne rfl
      · intro h; exact absurd he₀ h
    · intro τ _ hne
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg]
      rintro ⟨-, hper⟩
      exact hne (hper.unique hc₀.2)
    · intro h; exact absurd hτ₀ h
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · exact tripChargeW_nonneg hv l
    · intro τ hτ
      apply Finset.sum_eq_zero
      intro e he
      rw [if_neg (hex τ hτ e he)]

/-- **`prop:excess`, overdue part**: the excess of the overdue services is at most `(3/2) ∑ C_{j,W}` plus `(L + 4)` times the comparator's fetch cost, where `∑ C_{j,W}` is at most the total weight of the chargeable round trips. -/
theorem sum_excess_overdue_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (hSw : Schedule.SwapForm input S)
    (hF : S.FeasibleBy input σ) :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then excessAt input S i else 0) ≤
      3 / 2 * ∑ i ∈ Finset.range (log input).length, tripChargeW input σ S i +
        (L + 4) * S.fetchCost input := by
  set N := (log input).length with hN
  set R : ℕ → ℝ := fun i => ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
      (if i ∈ lightServices input σ S τ e then levelLenAt input i e else 0) with hRdef
  have hRnn : ∀ i, 0 ≤ R i := by
    intro i
    apply Finset.sum_nonneg; intro τ _
    apply Finset.sum_nonneg; intro e _
    split_ifs
    · exact levelLenAt_nonneg i e
    · exact le_rfl
  -- Step A: each excess is the sum of its terms over its period and its levels
  have hA : ∀ i ∈ Finset.range N,
      (if IsOverdue input σ S i then excessAt input S i else 0) ≤ R i := by
    intro i hi
    have hi' : i < N := Finset.mem_range.1 hi
    split_ifs with hov
    swap
    · exact hRnn i
    have hov' := hov
    obtain ⟨h, p, hm, q, hwq, hovq⟩ := hov'
    unfold excessAt
    rw [dif_pos hi', hm]
    try simp only
    split_ifs with hmem
    · exact hRnn i
    by_cases hex : ∃ τ, InPer S τ (entryTime input i)
    · obtain ⟨τ₀, hτ₀⟩ := hex
      have hcache := Schedule.InPer.cacheAt_eq hv hSw hτ₀
      calc ∑ e ∈ excessLevels input S p (entryTime input i),
            levelLen input (snapAt input i).x p e
          = ∑ e ∈ lightLevels input S τ₀,
              (if i ∈ lightServices input σ S τ₀ e then levelLenAt input i e else 0) := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext e
              simp only [excessLevels, lightLevels, lightServices, Finset.mem_filter,
                Finset.mem_Icc, Finset.mem_range, hcache, isLightService_iff hi' hm]
              constructor
              · rintro ⟨⟨h1, h2⟩, h3⟩
                exact ⟨⟨⟨(minLevel_le p).trans h1, h2⟩, h3⟩, hi', h1, hov, hτ₀⟩
              · rintro ⟨⟨⟨-, h2⟩, h3⟩, -, h1, -⟩
                exact ⟨⟨h1, h2⟩, h3⟩
            · intro e _
              rw [levelLenAt_of_critical hi' hm]
        _ ≤ R i := Finset.single_le_sum (f := fun τ => ∑ e ∈ lightLevels input S τ,
              (if i ∈ lightServices input σ S τ e then levelLenAt input i e else 0))
            (fun τ _ => by
              apply Finset.sum_nonneg; intro e _
              split_ifs
              · exact levelLenAt_nonneg i e
              · exact le_rfl) hτ₀.1
    · -- no step before the service: then it has no excess levels
      push_neg at hex
      have hall : ∀ step ∈ S, entryTime input i < step.time := by
        intro s hs
        by_contra hle
        push_neg at hle
        obtain ⟨τ, hτ⟩ := Schedule.InPer.exists_of_step ⟨s, hs, hle⟩
        exact hex τ hτ
      have hC0 := Schedule.cacheAt_of_lt hv hSw hall
      have hempty : excessLevels input S p (entryTime input i) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        simp only [excessLevels, Finset.mem_filter, Finset.mem_Icc] at he
        obtain ⟨⟨hle, -⟩, hlt⟩ := he
        obtain ⟨r, -, hrq, hrs⟩ := exists_served_of_overdue hv hovq
        obtain ⟨s, -, -, hst, hcase⟩ := hrs
        rcases hcase with ⟨hC, -⟩ | ⟨j, hj, hjt, -, -⟩
        · have hq : q ∈ cacheAt input S (entryTime input i) := by
            rw [hC0]; rw [← hrq]; exact hC
          have h1 := hlt q hq
          have h2 := (level_le_iff' hv p e).1 hle
          linarith
        · have := hall _ (List.getElem_mem hj)
          linarith
      rw [hempty, Finset.sum_empty]
      exact hRnn i
  -- Step B: regroup by periods and levels
  have hB : ∑ i ∈ Finset.range N, R i =
      ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
        ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e := by
    simp only [hRdef]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro τ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2
      (by unfold lightServices; exact Finset.filter_subset _ _)]
  -- Step C: `lem:periodlevel` for every period and level
  have hC : ∀ τ ∈ stepTimes S, ∀ e ∈ lightLevels input S τ,
      ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e ≤
        (L + 4) * levelWeight e +
          3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l := by
    intro τ _ e he
    simp only [lightLevels, Finset.mem_filter, Finset.mem_Icc] at he
    have := periodLevel_sum hv hσ hSw hF he.2 he.1.2
    linarith
  -- Step E: `lem:lightest`
  have hE : ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ, levelWeight e ≤
      S.fetchCost input := by
    apply Schedule.sum_stepTimes_le hv hSw hF
    intro τ _ q hq
    have hlw := PagingWithDelay.PMD.levelWeight_level hv
      h2 q
    rw [← hlw]
    apply le_of_lt
    apply sum_levelWeight_lt
    intro e he
    simp only [lightLevels, Finset.mem_filter] at he
    exact lt_of_levelWeight_lt ((he.2 q hq).trans_eq hlw.symm)
  -- Step F: the chargeable round trips
  have hFt := sum_periodTrips_le (σ := σ) (S := S) hv
  -- combine
  have hk1 : 0 ≤ L + 4 := by have := L_nonneg' input; linarith
  have hk2 : (0 : ℝ) ≤ 3 / 2 := by norm_num
  calc ∑ i ∈ Finset.range N, (if IsOverdue input σ S i then excessAt input S i else 0)
      ≤ ∑ i ∈ Finset.range N, R i := Finset.sum_le_sum hA
    _ = ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
          ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e := hB
    _ ≤ ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
          ((L + 4) * levelWeight e +
            3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l) :=
        Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun e he => hC τ hτ e he
    _ = (L + 4) * ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ, levelWeight e +
          3 / 2 * ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
            ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hE hk1
        have := mul_le_mul_of_nonneg_left hFt hk2
        linarith

end

end ExcessProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Analysis.AlgDelay.Run` -/
section

/-!
# `prop:algdelay`, part 1: facts about the run

Facts about the log of `PMD` used by the proof of `prop:algdelay` (`PagingWithDelay/Analysis/AlgDelay.lean`):

* `startOf j`: the *start index* of the time of entry `j`, the last tick or advance at or before `j`. All entries from `startOf j` to `j` have the same time.
* Visits (`visitPage`): a visit has a pending request on its page, and no request on its page is pending after it; no page is visited twice at one time.
* Between the start of a time and a visit of `p`, the delay of `p` does not change and the claim of `p` does not decrease.
* `exists_chain`: between two log indices, the base state changes only by critical services, so it is the end of a chain (`chainState`) of them, whose length (`chainLen`) is the sum of the `lenAt` of the entries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

/-! ### Chains of critical services -/

theorem chainState_append_single (I : Instance Page) (x : Page → ℝ)
    (ps : List Page) (p : Page) :
    chainState I x (ps ++ [p]) = criticalState I (chainState I x ps) p := by
  induction ps generalizing x with
  | nil => rfl
  | cons a ps ih => simp [ih]

theorem chainLen_append_single (I : Instance Page) (x : Page → ℝ)
    (ps : List Page) (p : Page) :
    chainLen I x (ps ++ [p]) = chainLen I x ps + serviceEnd I (chainState I x ps) p := by
  induction ps generalizing x with
  | nil => simp
  | cons a ps ih => simp [ih]; ring

/-! ### The accounting of single entries -/

theorem lenAt_of_critical {l : ℕ} (h : l < (log input).length) {p : Page}
    (hm : moveAt l h = .critical p) :
    lenAt input l = serviceEnd input (snapAt input l).x p := by
  simp [lenAt, h, hm]

theorem lenAt_of_not_critical {l : ℕ}
    (hm : ∀ (h : l < (log input).length) p, moveAt l h ≠ .critical p) : lenAt input l = 0 := by
  unfold lenAt
  split_ifs with h
  · rcases hc : moveAt l h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp
    exact absurd hc (hm h p)
  · rfl

theorem lenAt_nonneg (l : ℕ) : 0 ≤ lenAt input l := by
  unfold lenAt
  split_ifs with h
  · split
    · exact serviceEnd_nonneg' _ _
    all_goals exact le_rfl
  · exact le_rfl

theorem holeAt_of_openHole {l : ℕ} (h : l < (log input).length) {e : ℤ}
    (hm : moveAt l h = .openHole e) : holeAt input l = holePayment input e := by
  simp [holeAt, h, hm]

theorem holeAt_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ holeAt input l := by
  unfold holeAt
  split_ifs with h
  · split
    · unfold holePayment
      have := Instance.delta_lt_one hv
      apply mul_nonneg (PagingWithDelay.PMD.levelWeight_pos _).le
      linarith
    all_goals exact le_rfl
  · exact le_rfl

/-! ### Visits -/

theorem visitPage_eq_some_iff {j : ℕ} {p : Page} :
    visitPage input j = some p ↔ ∃ h : j < (log input).length,
      moveAt j h = .critical p ∨ ∃ e π, moveAt j h = .trip e π ∧ π.page = p := by
  unfold visitPage
  split_ifs with h
  · rcases hm : moveAt j h with t | t | p' | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp [h, hm, eq_comm]
  · simp [h]

theorem visitPage_of_critical {j : ℕ} (h : j < (log input).length) {p : Page}
    (hm : moveAt j h = .critical p) : visitPage input j = some p :=
  visitPage_eq_some_iff.mpr ⟨h, Or.inl hm⟩

theorem visitPage_of_trip {j : ℕ} (h : j < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt j h = .trip e π) : visitPage input j = some π.page :=
  visitPage_eq_some_iff.mpr ⟨h, Or.inr ⟨e, π, hm, rfl⟩⟩

theorem visitPage_eq_none {j : ℕ} (hn : visitPage input j = none) (h : j < (log input).length) :
    (∀ p, moveAt j h ≠ .critical p) ∧ (∀ e π, moveAt j h ≠ .trip e π) := by
  refine ⟨fun p hp => ?_, fun e π hp => ?_⟩
  · rw [visitPage_of_critical h hp] at hn; cases hn
  · rw [visitPage_of_trip h hp] at hn; cases hn

/-- The fetch cost `w_p (x_p - δ)` of a visit of `p` is its `fetchAt` (critical service) or its `tripAt` (round trip). -/
theorem fetchAt_add_tripAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    fetchAt input j + tripAt input j = w p * ((snapAt input j).x p - δ) := by
  obtain ⟨h, hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
  · simp [fetchAt, tripAt, h, hm, PagingWithDelay.PMD.criticalFetch]
  · simp [fetchAt, tripAt, h, hm, tripCost]

theorem fetchAt_add_tripAt_of_none {j : ℕ} (hn : visitPage input j = none) :
    fetchAt input j + tripAt input j = 0 := by
  unfold fetchAt tripAt
  split_ifs with h
  · obtain ⟨h1, h2⟩ := visitPage_eq_none hn h
    rcases hm : moveAt j h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp
    · exact absurd hm (h1 p)
    · exact absurd hm (h2 e π)
  · simp

section

variable (hv : input.Valid)
include hv

/-- A visit of `p` has a pending request on `p`. -/
theorem visit_pending {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    ∃ ρ ∈ (snapAt input j).pending, ρ.page = p := by
  obtain ⟨h, hm | ⟨e, π, hm, hπ⟩⟩ := visitPage_eq_some_iff.mp hvis
  · exact (critical_facts hv h hm).2.1
  · obtain ⟨-, hc, -⟩ := trip_spec hv h hm
    unfold tripCandidate at hc
    have := List.argmin_mem hc
    exact ⟨π, (List.mem_filter.mp this).1, hπ⟩

/-- After a visit of `p`, no request on `p` is pending. -/
theorem no_pending_after_visit {l : ℕ} {p : Page} (hvis : visitPage input l = some p)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input (l + 1)).pending) : ρ.page ≠ p := by
  obtain ⟨h, hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
  · exact ((pending_succ_of_critical hv h hm).mp hρ).2
  · exact ((pending_succ_of_trip hv h hm).mp hρ).2

/-- Without ticks, the pending list only shrinks. -/
theorem pending_of_no_tick {l m : ℕ} (hlm : l ≤ m)
    (hno : ∀ l' (h : l' < (log input).length), l ≤ l' → l' < m → ∀ t, moveAt l' h ≠ .tick t)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input m).pending) : ρ ∈ (snapAt input l).pending := by
  induction m, hlm using Nat.le_induction generalizing ρ with
  | base => exact hρ
  | succ m hm ih =>
    apply ih (fun l' h h1 h2 => hno l' h h1 (by omega))
    by_contra hnot
    by_cases hlt : m < (log input).length
    · exact hno m hlt hm (by omega) _ (pending_new hv hlt hρ hnot).1
    · rw [snapAt_of_ge (by omega)] at hρ
      rw [snapAt_of_ge (by omega)] at hnot
      exact hnot hρ

end

/-! ### Start indices -/

variable (input) in
/-- Entry `a` is a tick or an advance: the entries after it (until the next one) happen at its time. -/
def IsTA (a : ℕ) : Prop :=
  ∃ h : a < (log input).length, (∃ t, moveAt a h = .tick t) ∨ (∃ t, moveAt a h = .advance t)


variable (input) in
/-- The *start index* of the time of entry `j`: the last tick or advance at or before `j`. (Well defined, since entry `0` is a tick.) -/
def startOf (j : ℕ) : ℕ := Nat.findGreatest (IsTA input) j

theorem startOf_le (j : ℕ) : startOf input j ≤ j := Nat.findGreatest_le j

theorem not_isTA_of_startOf_lt {j l : ℕ} (h1 : startOf input j < l) (h2 : l ≤ j) :
    ¬ IsTA input l :=
  Nat.findGreatest_is_greatest h1 h2

theorem startOf_eq_of {a j : ℕ} (ha : IsTA input a) (haj : a ≤ j)
    (hno : ∀ l, a < l → l ≤ j → ¬ IsTA input l) : startOf input j = a :=
  Nat.findGreatest_eq_iff.mpr ⟨haj, fun _ => ha, fun n h1 h2 => hno n h1 h2⟩

theorem not_tick_of_not_isTA {l : ℕ} (hl : ¬ IsTA input l) (h : l < (log input).length) :
    (∀ t, moveAt l h ≠ .tick t) ∧ (∀ t, moveAt l h ≠ .advance t) :=
  ⟨fun t ht => hl ⟨h, Or.inl ⟨t, ht⟩⟩, fun t ht => hl ⟨h, Or.inr ⟨t, ht⟩⟩⟩

theorem not_isTA_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    ¬ IsTA input j := by
  rintro ⟨h, ⟨t, ht⟩ | ⟨t, ht⟩⟩ <;>
  · obtain ⟨h', hm | ⟨e, π, hm, -⟩⟩ := visitPage_eq_some_iff.mp hvis
    · rw [ht] at hm; cases hm
    · rw [ht] at hm; cases hm

section

variable (hv : input.Valid)
include hv

theorem isTA_startOf {j : ℕ} (hj : j < (log input).length) : IsTA input (startOf input j) := by
  have h0 : 0 < (log input).length := by omega
  obtain ⟨t, ht⟩ := first_tick hv h0
  exact Nat.findGreatest_spec (Nat.zero_le j) ⟨h0, Or.inl ⟨t, ht⟩⟩

theorem startOf_of_between {j l : ℕ} (hj : j < (log input).length) (h1 : startOf input j ≤ l)
    (h2 : l ≤ j) : startOf input l = startOf input j :=
  startOf_eq_of (isTA_startOf hv hj) h1 (fun l' h1' h2' => not_isTA_of_startOf_lt h1' (by omega))

theorem startOf_lt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    startOf input j < j := by
  obtain ⟨h, -⟩ := visitPage_eq_some_iff.mp hvis
  rcases lt_or_eq_of_le (startOf_le (input := input) j) with hlt | heq
  · exact hlt
  · exact absurd (heq ▸ isTA_startOf hv h) (not_isTA_of_visit hvis)

/-- All entries from the start index of `j` to `j` have the time of `j`. -/
theorem entryTime_startOf {j : ℕ} (hj : j < (log input).length) :
    entryTime input j = entryTime input (startOf input j) := by
  have key : ∀ l, startOf input j ≤ l → l ≤ j → entryTime input l = entryTime input (startOf input j) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => intro _; rfl
    | succ l hl ih =>
      intro hlj
      have hlt : l + 1 < (log input).length := by omega
      obtain ⟨h1, h2⟩ := not_tick_of_not_isTA (not_isTA_of_startOf_lt (by omega) hlj) hlt
      rw [entryTime_of_not_tick hv hlt h1 h2, ← ih (by omega)]
      rfl
  exact key j (startOf_le j) le_rfl

/-- No page is visited twice at one time: between the start index of a visit of `p` and the visit, `p` is not visited. -/
theorem no_visit_between {j l : ℕ} {p : Page} (hvis : visitPage input j = some p)
    (h1 : startOf input j < l) (h2 : l < j) : visitPage input l ≠ some p := by
  intro hl
  obtain ⟨ρ, hρ, hρp⟩ := visit_pending hv hvis
  have hsub := pending_of_no_tick hv (l := l + 1) (m := j) (by omega)
    (fun l' h h1' h2' t ht => not_isTA_of_startOf_lt (j := j) (by omega) (by omega)
      ⟨h, Or.inl ⟨t, ht⟩⟩) hρ
  exact no_pending_after_visit hv hl hsub hρp

/-- No visit of `p` in `[startOf j, j)` for a visit `j` of `p`. -/
theorem no_visit_before {j l : ℕ} {p : Page} (hvis : visitPage input j = some p)
    (h1 : startOf input j ≤ l) (h2 : l < j) : visitPage input l ≠ some p := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact no_visit_between hv hvis h1 h2
  · intro hl
    have hlt : l < (log input).length := (visitPage_eq_some_iff.mp hl).1
    have := isTA_startOf hv (visitPage_eq_some_iff.mp hvis).1
    rw [h1] at this
    exact not_isTA_of_visit hl this

/-! ### Delays and claims between visits -/

/-- A move that is not a tick and not a visit of `p` does not change the delay of `p`. -/
theorem pageDelay_succ {l : ℕ} (h : l < (log input).length) (htk : ∀ t, moveAt l h ≠ .tick t)
    {p : Page} (hp : visitPage input l ≠ some p) (t : ℝ) :
    pageDelay (snapAt input (l + 1)).pending p t = pageDelay (snapAt input l).pending p t := by
  rcases hm : moveAt l h with t' | t' | p' | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · exact absurd hm (htk t')
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · have hp' : p ≠ p' := fun hpp => hp (hpp ▸ visitPage_of_critical h hm)
    rw [(critical_spec hv h hm).2.2]
    exact pageDelay_filter_ne _ hp' t
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · have hp' : p ≠ π.page := fun hpp => hp (hpp ▸ visitPage_of_trip h hm)
    rw [(trip_spec hv h hm).2.2.2]
    exact pageDelay_filter_ne _ hp' t
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]

theorem pageDelay_of_between {l m : ℕ} (hlm : l ≤ m) {p : Page}
    (hno : ∀ l' (h : l' < (log input).length), l ≤ l' → l' < m →
      (∀ t, moveAt l' h ≠ .tick t) ∧ visitPage input l' ≠ some p) (t : ℝ) :
    pageDelay (snapAt input m).pending p t = pageDelay (snapAt input l).pending p t := by
  induction m, hlm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [← ih (fun l' h h1 h2 => hno l' h h1 (by omega))]
    by_cases hlt : m < (log input).length
    · obtain ⟨h1, h2⟩ := hno m hlt hm (by omega)
      exact pageDelay_succ hv hlt h1 h2 t
    · rw [snapAt_of_ge (by omega), snapAt_of_ge (i := m) (by omega)]

/-- A move that is not a visit of `p` does not decrease the claim of `p`. -/
theorem claims_le_succ {l : ℕ} {p : Page} (hp : visitPage input l ≠ some p) :
    (snapAt input l).claims p ≤ (snapAt input (l + 1)).claims p := by
  by_cases h : l < (log input).length
  · by_cases hvis : (∃ p', moveAt l h = .critical p') ∨ (∃ e π, moveAt l h = .trip e π)
    · rcases hvis with ⟨p', hm⟩ | ⟨e, π, hm⟩
      · have hp' : p ≠ p' := fun hpp => hp (hpp ▸ visitPage_of_critical h hm)
        rw [(critical_spec hv h hm).2.2]
        try dsimp only
        rw [Function.update_of_ne hp']
        exact le_claimUpdate hv _ _ _ _ _ _
      · have hp' : p ≠ π.page := fun hpp => hp (hpp ▸ visitPage_of_trip h hm)
        rw [(trip_spec hv h hm).2.2.2]
        try dsimp only
        rw [Function.update_of_ne hp']
    · push_neg at hvis
      rw [claims_succ_of_not_visit hv h hvis.1 hvis.2]
  · rw [snapAt_of_ge (i := l + 1) (by omega), snapAt_of_ge (i := l) (by omega)]

theorem claims_le_of_between {l m : ℕ} (hlm : l ≤ m) {p : Page}
    (hno : ∀ l', l ≤ l' → l' < m → visitPage input l' ≠ some p) :
    (snapAt input l).claims p ≤ (snapAt input m).claims p := by
  induction m, hlm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    exact (ih fun l' h1 h2 => hno l' h1 (by omega)).trans (claims_le_succ hv (hno m hm (by omega)))

/-! ### Chains of critical services along the run -/

/-- Between `a` and `m`, the base state changes only by critical services: it is the end of their chain, of total length `∑_{a ≤ l < m} lenAt l`. -/
theorem exists_chain {a m : ℕ} (ham : a ≤ m) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), a ≤ l → l < m → moveAt l hl ≠ .critical q) :
    ∃ ps : List Page, q ∉ ps ∧
      baseState (snapAt input m) = chainState input (baseState (snapAt input a)) ps ∧
      chainLen input (baseState (snapAt input a)) ps = ∑ l ∈ Finset.Ico a m, lenAt input l := by
  induction m, ham using Nat.le_induction with
  | base => exact ⟨[], by simp, rfl, by simp⟩
  | succ m hm ih =>
    obtain ⟨ps, hq, hst, hlen⟩ := ih fun l hl h1 h2 => hno l hl h1 (by omega)
    rw [Finset.sum_Ico_succ_top hm]
    by_cases hlt : m < (log input).length
    · by_cases hc : ∃ p, moveAt m hlt = .critical p
      · obtain ⟨p, hp⟩ := hc
        have hpq : p ≠ q := fun h => hno m hlt hm (by omega) (h ▸ hp)
        obtain ⟨hidle, -, heq⟩ := critical_spec hv hlt hp
        have hxm : (snapAt input m).x = baseState (snapAt input m) :=
          x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
        have hb1 : baseState (snapAt input (m + 1)) = criticalState input (snapAt input m).x p := by
          rw [baseState_of_not_preempt (by rw [heq]; intro e b hb; cases hb), heq]
        refine ⟨ps ++ [p], ?_, ?_, ?_⟩
        · simp [hq, hpq.symm]
        · rw [hb1, chainState_append_single, hxm, hst]
        · rw [chainLen_append_single, hlen, lenAt_of_critical hlt hp, hxm, hst]
      · push_neg at hc
        refine ⟨ps, hq, ?_, ?_⟩
        · rw [baseState_succ_of_not_critical hv hlt hc, hst]
        · rw [lenAt_of_not_critical (fun h p => hc p), add_zero, hlen]
    · refine ⟨ps, hq, ?_, ?_⟩
      · rw [snapAt_of_ge (by omega), ← snapAt_of_ge (i := m) (by omega), hst]
      · rw [lenAt_of_not_critical (fun h p => absurd h hlt), add_zero, hlen]

end

end

end PagingWithDelay.PMD.DelayProof
end

/-! ## Inlined from `PagingWithDelay.Analysis.AlgDelay.Bridge` -/
section

/-!
# `prop:algdelay`, part 2: from the fractional delay cost to the visits

The fractional delay cost of `PMD` (`FracSchedule.delayCost`) is a sum over the request list. Every request is either served on arrival (cost `d(0) = 0`) or pending until the visit of its page that serves it. We bound the delay cost by the sum over the visits `j` of the delays of the requests served by `j`, each weighted with the missing mass `x_p - δ` of the page right before the visit (`delayCost_le_sum_visitDelay`):

* `stateBefore_tick`: the state right before the arrival time `a` of a request is the state before the tick at `a`;
* by `obs:monotone`, the weight `α_ρ` of a request is at most `x_p - δ` right before its serving visit;
* multiplicities: the request list may contain equal requests; each occurs in the pending list at its serving visit at least as often as in the request list (`count_requests_le_pending`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest lastState)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

/-! ### Definitions -/

variable (input) in
/-- The requests served by entry `j`: the pending requests on the page it visits (none if it is not a visit). -/
def servedAt (j : ℕ) : List (Request Page) :=
  match visitPage input j with
  | some p => (snapAt input j).pending.filter fun ρ => decide (ρ.page = p)
  | none => []

variable (input) in
open scoped PagingWithDelay.InstanceNotation in
/-- The delay of `ρ` at the time of entry `j`, weighted with the missing mass `x_p - δ` of its page right before entry `j`. -/
def reqCost (j : ℕ) (ρ : Request Page) : ℝ :=
  ((snapAt input j).x ρ.page - δ) * ρ.delay (entryTime input j - ρ.arrival)

variable (input) in
/-- The weighted delay of the requests served by entry `j`. -/
def visitDelay (j : ℕ) : ℝ := ((servedAt input j).map (reqCost input j)).sum

theorem mem_servedAt {j : ℕ} {ρ : Request Page} (h : ρ ∈ servedAt input j) :
    ρ ∈ (snapAt input j).pending ∧ visitPage input j = some ρ.page := by
  unfold servedAt at h
  split at h
  · rename_i p hp
    simp only [List.mem_filter, decide_eq_true_eq] at h
    exact ⟨h.1, h.2 ▸ hp⟩
  · simp at h

theorem servedAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    servedAt input j = (snapAt input j).pending.filter fun ρ => decide (ρ.page = p) := by
  simp [servedAt, hvis]

theorem servedAt_of_none {j : ℕ} (hvis : visitPage input j = none) : servedAt input j = [] := by
  simp [servedAt, hvis]

open scoped PagingWithDelay.InstanceNotation in
/-- The weighted delay of a visit of `p` is `(x_p - δ) · delay_p(t)`. -/
theorem visitDelay_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    visitDelay input j = ((snapAt input j).x p - δ) *
      pageDelay (snapAt input j).pending p (entryTime input j) := by
  unfold visitDelay pageDelay
  rw [servedAt_of_visit hvis, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ρ hρ
  simp only [List.mem_filter, decide_eq_true_eq] at hρ
  simp [reqCost, hρ.2]

theorem visitDelay_of_none {j : ℕ} (hvis : visitPage input j = none) : visitDelay input j = 0 := by
  simp [visitDelay, servedAt_of_none hvis]

/-! ### The state right before an arrival -/

theorem lastState_eq_getLast : ∀ (y : Page → ℝ) (A : List (Waypoint Page)) (h : A ≠ []),
    lastState y A = (A.getLast h).state
  | _, [], h => absurd rfl h
  | _, [a], _ => rfl
  | y, a :: b :: rest, _ => by
    rw [PagingWithDelay.PMD.lastState_cons, lastState_eq_getLast a.state (b :: rest)
      (List.cons_ne_nil _ _)]
    rfl

section

variable (hv : input.Valid)
include hv

theorem mem_take_flatMap {m : ℕ} {w : Waypoint Page}
    (hw : w ∈ ((log input).take m).flatMap fun e => waypoints input e.1 e.2) :
    ∃ l, l < m ∧ ∃ h : l < (log input).length, w ∈ wpAt input l := by
  rw [List.mem_flatMap] at hw
  obtain ⟨e, he, hwe⟩ := hw
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hl
  have hl1 : l < m := lt_of_lt_of_le hl (min_le_left _ _)
  have hl2 : l < (log input).length := lt_of_lt_of_le hl (min_le_right _ _)
  refine ⟨l, hl1, hl2, ?_⟩
  rw [List.getElem_take, log_getElem l hl2] at hwe
  rw [wpAt_of_lt hl2]
  exact hwe

theorem mem_drop_flatMap {m : ℕ} {w : Waypoint Page}
    (hw : w ∈ ((log input).drop m).flatMap fun e => waypoints input e.1 e.2) :
    ∃ l, m ≤ l ∧ ∃ h : l < (log input).length, w ∈ wpAt input l := by
  rw [List.mem_flatMap] at hw
  obtain ⟨e, he, hwe⟩ := hw
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
  rw [List.length_drop] at hl
  have hl2 : m + l < (log input).length := by omega
  refine ⟨m + l, by omega, hl2, ?_⟩
  rw [List.getElem_drop, log_getElem (m + l) hl2] at hwe
  rw [wpAt_of_lt hl2]
  exact hwe

/-- The state right before the arrival time `t` (in the sense of `FracSchedule.stateBefore`) is the state before the tick at `t`. -/
theorem stateBefore_tick {i₀ : ℕ} (h₀ : i₀ < (log input).length) {t : ℝ}
    (ht : moveAt i₀ h₀ = .tick t) :
    FracSchedule.stateBefore (preemptiveMirrorDescent input) t = (snapAt input i₀).x := by
  set W : Entry Page → List (Waypoint Page) := fun e => waypoints input e.1 e.2 with hW
  set A := ((log input).take i₀).flatMap W with hA
  set B := ((log input).drop i₀).flatMap W with hB
  have hXAB : preemptiveMirrorDescent input = A ++ B := by
    rw [output_eq hv, hA, hB, ← List.flatMap_append, List.take_append_drop]
  have hAt : ∀ w ∈ A, w.time < t := by
    intro w hw
    obtain ⟨l, hl, hl', hwl⟩ := mem_take_flatMap hv hw
    rw [(wp_spec hv l hl' w hwl).1]
    exact entryTime_lt_of_tick hv h₀ ht hl
  have hBt : ∀ w ∈ B, ¬ w.time < t := by
    intro w hw
    obtain ⟨l, hl, hl', hwl⟩ := mem_drop_flatMap hv hw
    rw [(wp_spec hv l hl' w hwl).1, not_lt, ← entryTime_tick hv h₀ ht]
    exact entryTime_mono hv hl
  have hfilter : (preemptiveMirrorDescent input).filter (fun w => decide (w.time < t)) = A := by
    rw [hXAB, List.filter_append, List.filter_eq_self.mpr (fun w hw => by simpa using hAt w hw),
      List.filter_eq_nil_iff.mpr (fun w hw => by simpa using hBt w hw), List.append_nil]
  have hlast : lastState (snapAt input 0).x A = (snapAt input i₀).x :=
    (pathFrom_take (fun _ _ => 0) (lastState_wpAt hv) i₀ h₀.le).2
  unfold FracSchedule.stateBefore
  rw [hfilter]
  by_cases hAe : A = []
  · rw [hAe] at hlast ⊢
    simp only [List.getLast?_nil]
    rw [PagingWithDelay.PMD.lastState_nil] at hlast
    rw [← hlast]
    have hmem : (⟨t, (snapAt input i₀).x⟩ : Waypoint Page) ∈ preemptiveMirrorDescent input := by
      rw [mem_output_iff hv]
      exact ⟨i₀, h₀, by rw [wpAt_of_lt h₀, ht]; simp [waypoints]⟩
    cases hhd : (preemptiveMirrorDescent input).head? with
    | none =>
      rw [List.head?_eq_none_iff] at hhd
      rw [hhd] at hmem; simp at hmem
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      exact output_head hv w (by rw [← output_eq hv]; exact hhd)
  · rw [List.getLast?_eq_some_getLast hAe]
    try dsimp only
    rw [← lastState_eq_getLast (snapAt input 0).x A hAe, hlast]

/-! ### Multiplicities -/

/-- A request that stays pending does not lose copies. -/
theorem count_pending_succ {l : ℕ} (h : l < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (l + 1)).pending) :
    (snapAt input l).pending.count ρ ≤ (snapAt input (l + 1)).pending.count ρ := by
  rcases hm : moveAt l h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · have heq := (tick_spec hv h hm).2.2.2.2
    rw [heq] at hρ ⊢
    try dsimp only at hρ ⊢
    rw [List.count_filter, List.count_append]
    · omega
    · exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [(critical_spec hv h hm).2.2] at hρ ⊢
    try dsimp only at hρ ⊢
    rw [List.count_filter]
    exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [(trip_spec hv h hm).2.2.2] at hρ ⊢
    try dsimp only at hρ ⊢
    rw [List.count_filter]
    exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]

/-- At the tick of its arrival, a request that becomes pending enters the pending list with all its copies in the request list. -/
theorem count_requests_le_tick {i₀ : ℕ} (h₀ : i₀ < (log input).length) {ρ : Request Page}
    (ht : moveAt i₀ h₀ = .tick ρ.arrival) (hρ : ρ ∈ (snapAt input (i₀ + 1)).pending) :
    input.requests.count ρ ≤ (snapAt input (i₀ + 1)).pending.count ρ := by
  have heq := (tick_spec hv h₀ ht).2.2.2.2
  rw [heq] at hρ ⊢
  try dsimp only at hρ ⊢
  rw [List.count_filter, List.count_append, List.count_filter]
  · omega
  · simp
  · exact (List.mem_filter.mp hρ).2

theorem count_requests_le_pending {i₀ j : ℕ} (h₀ : i₀ < (log input).length) {ρ : Request Page}
    (ht : moveAt i₀ h₀ = .tick ρ.arrival) (hij : i₀ < j)
    (hpend : ∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending) :
    input.requests.count ρ ≤ (snapAt input j).pending.count ρ := by
  induction j, hij using Nat.le_induction with
  | base => exact count_requests_le_tick hv h₀ ht (hpend _ (by omega) le_rfl)
  | succ m hm ih =>
    refine (ih fun l h1 h2 => hpend l h1 (by omega)).trans ?_
    by_cases hlt : m < (log input).length
    · exact count_pending_succ hv hlt (hpend _ (by omega) le_rfl)
    · rw [snapAt_of_ge (i := m + 1) (by omega), snapAt_of_ge (i := m) (by omega)]

/-! ### The bridge -/

theorem reqCost_nonneg {j : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input j).pending) :
    0 ≤ reqCost input j ρ := by
  obtain ⟨hreq, harr, -⟩ := pending_spec hv hρ
  have hx := delta_lt_of_pending hv hρ
  have hd : 0 ≤ ρ.delay (entryTime input j - ρ.arrival) := by
    rw [← hv.delay_zero ρ hreq]
    exact hv.delay_mono ρ hreq (by linarith [now_le_entryTime hv j])
  exact mul_nonneg (by linarith) hd

theorem visitDelay_eq_sum_count (j : ℕ) :
    visitDelay input j =
      ∑ ρ ∈ input.requests.toFinset, ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
  unfold visitDelay
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro ρ hρ
    rw [List.mem_toFinset] at hρ ⊢
    exact (pending_spec hv (mem_servedAt hρ).1).1
  · intro ρ _ hρ
    rw [List.mem_toFinset] at hρ
    rw [List.count_eq_zero_of_not_mem hρ]
    simp

open scoped PagingWithDelay.InstanceNotation in
/-- The delay cost of one request (counted with its multiplicity) is at most what the visits charge for it. -/
theorem request_le {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    (input.requests.count ρ : ℝ) *
        ((FracSchedule.stateBefore (preemptiveMirrorDescent input) ρ.arrival ρ.page -
            δ) *
          ρ.delay (FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ -
            ρ.arrival)) ≤
      ∑ j ∈ Finset.range (log input).length,
        ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
  obtain ⟨i₀, j, h₀, hj, ht, hij, hpend, hnot, hserv⟩ := serviceTime_spec hv hρ
  have hnonneg : ∀ j' ∈ Finset.range (log input).length,
      0 ≤ ((servedAt input j').count ρ : ℝ) * reqCost input j' ρ := by
    intro j' _
    by_cases hc : (servedAt input j').count ρ = 0
    · simp [hc]
    · have hmem : ρ ∈ servedAt input j' := List.count_pos_iff.mp (Nat.pos_of_ne_zero hc)
      exact mul_nonneg (Nat.cast_nonneg _) (reqCost_nonneg hv (mem_servedAt hmem).1)
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst heq
    rw [hserv, entryTime_tick hv h₀ ht, sub_self, hv.delay_zero ρ hρ, mul_zero, mul_zero]
    exact Finset.sum_nonneg hnonneg
  · have hρj := hpend j hlt le_rfl
    obtain ⟨hvis, -⟩ := pending_removed hv hj hρj hnot
    have hvp : visitPage input j = some ρ.page := by
      rcases hvis with hm | ⟨e, π, hm, hπ⟩
      · exact visitPage_of_critical hj hm
      · rw [← hπ]; exact visitPage_of_trip hj hm
    have hcount : (servedAt input j).count ρ = (snapAt input j).pending.count ρ := by
      rw [servedAt_of_visit hvp, List.count_filter (by simp)]
    have hcR := count_requests_le_pending hv h₀ ht hlt hpend
    have hx : (snapAt input i₀).x ρ.page ≤ (snapAt input j).x ρ.page := by
      rw [x_eq_baseState hv (fun e b hb => by rw [(tick_spec hv h₀ ht).1] at hb; cases hb)]
      apply baseState_le_x_of_mono hv hij
      intro l hl h1 h2 hm
      exact ((pending_succ_of_critical hv hl hm).mp (hpend (l + 1) (by omega) (by omega))).2 rfl
    have hd : 0 ≤ ρ.delay (entryTime input j - ρ.arrival) := by
      rw [← hv.delay_zero ρ hρ]
      apply hv.delay_mono ρ hρ
      have := entryTime_mono hv hij
      rw [entryTime_tick hv h₀ ht] at this
      linarith
    have hF : (FracSchedule.stateBefore (preemptiveMirrorDescent input) ρ.arrival ρ.page -
          δ) *
          ρ.delay (FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ -
            ρ.arrival) ≤ reqCost input j ρ := by
      rw [hserv, stateBefore_tick hv h₀ ht]
      exact mul_le_mul_of_nonneg_right (by linarith) hd
    have hF0 : 0 ≤ reqCost input j ρ := reqCost_nonneg hv hρj
    calc _ ≤ (input.requests.count ρ : ℝ) * reqCost input j ρ :=
          mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)
      _ ≤ ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
          apply mul_le_mul_of_nonneg_right _ hF0
          rw [hcount]; exact_mod_cast hcR
      _ ≤ _ := Finset.single_le_sum hnonneg (Finset.mem_range.mpr hj)

/-- **The bridge**: the fractional delay cost of `PMD` is at most the total weighted delay of the requests served by the visits. -/
theorem delayCost_le_sum_visitDelay :
    FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      ∑ j ∈ Finset.range (log input).length, visitDelay input j := by
  unfold FracSchedule.delayCost
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => visitDelay_eq_sum_count hv j, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [List.mem_toFinset] at hρ
  exact request_le hv hρ

end

end

end PagingWithDelay.PMD.DelayProof
end

/-! ## Inlined from `PagingWithDelay.Analysis.AlgDelay.Visit` -/
section

/-!
# `prop:algdelay`, part 3: the delay of one visit, and the used delay

Consider a visit `j` of page `p` at time `t`, and let `a = startOf j` be the tick or advance that set `t`. No page has triggered since the previous time, so `snapAt a` is the paper's state "right before the steps of `PMD` at time `t`". Let `ō_p = o_p(t)` be the overshoot of `p` in this state (`overAt j`). The visit pays

  `(x_p - δ) · delay_p(t) ≤ c_p + (x_p - δ) w_p + ō_p` (`visitDelay_le`),

where `c_p` is the claim of `p` right before the visit (`claimAt j`) and `(x_p - δ) w_p` is the fetch cost of the visit (`fetchAt j + tripAt j`).

The claims of all visits sum to at most `∑_λ |λ| / L` (`sum_claimAt_le`), by the potential `∑_q c_q`: a critical service increases it by `|λ|/L` minus the claim of its page, which it resets, and a round trip resets the claim of its page.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

variable (input) in
/-- The claim `c_p` of the page `p` visited by entry `j`, right before the visit (`0` if entry `j` is not a visit). -/
def claimAt (j : ℕ) : ℝ :=
  match visitPage input j with
  | some p => (snapAt input j).claims p
  | none => 0

variable (input) in
/-- The overshoot `ō_p = o_p(t)` of the page `p` visited by entry `j` at its time `t`, in the state at the start index of `t` (right before the steps of `PMD` at `t`); `0` if entry `j` is not a visit. -/
def overAt (j : ℕ) : ℝ :=
  match visitPage input j with
  | some p => overshoot input (snapAt input (startOf input j)).pending
      (snapAt input (startOf input j)).claims p (entryTime input j)
  | none => 0

theorem overAt_nonneg (j : ℕ) : 0 ≤ overAt input j := by
  unfold overAt
  split
  · exact overshoot_nonneg _ _ _ _
  · exact le_rfl

theorem overAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    overAt input j = overshoot input (snapAt input (startOf input j)).pending
      (snapAt input (startOf input j)).claims p (entryTime input j) := by
  simp [overAt, hvis]

theorem overAt_of_none {j : ℕ} (hvis : visitPage input j = none) : overAt input j = 0 := by
  simp [overAt, hvis]

section

variable (hv : input.Valid)
include hv

/-- A tick or an advance does not change the delays at its time: an advance does not change the pending list, and the requests arriving at a tick have delay `d(0) = 0`. -/
theorem pageDelay_succ_of_TA {a : ℕ} (h : a < (log input).length)
    (hmove : (∃ t, moveAt a h = .tick t) ∨ (∃ t, moveAt a h = .advance t)) (p : Page) :
    pageDelay (snapAt input (a + 1)).pending p (entryTime input a) =
      pageDelay (snapAt input a).pending p (entryTime input a) := by
  rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [entryTime_tick hv h ht, (tick_spec hv h ht).2.2.2.2]
    try dsimp only
    have hself : (snapAt input a).pending.filter
        (fun ρ => decide ((snapAt input a).x ρ.page ≠ δ)) = (snapAt input a).pending :=
      List.filter_eq_self.mpr (fun ρ hρ => by simpa using (ne_of_gt (delta_lt_of_pending hv hρ)))
    rw [List.filter_append, hself]
    unfold pageDelay
    rw [List.filter_append, List.map_append, List.sum_append, add_eq_left]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hy
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    rw [hρ.1.1.2, sub_self]
    exact hv.delay_zero ρ hρ.1.1.1
  · rw [(advance_spec hv h ht).2.2.2.2.2.2]

/-- **The delay of one visit**: `(x_p - δ) delay_p(t) ≤ c_p + (x_p - δ) w_p + ō_p`. -/
theorem visitDelay_le (j : ℕ) :
    visitDelay input j ≤ claimAt input j + (fetchAt input j + tripAt input j) + overAt input j := by
  cases hvis : visitPage input j with
  | none =>
    rw [visitDelay_of_none hvis, fetchAt_add_tripAt_of_none hvis, overAt_of_none hvis]
    simp [claimAt, hvis]
  | some p =>
    rw [visitDelay_of_visit hvis, fetchAt_add_tripAt_of_visit hvis, overAt_of_visit hvis]
    simp only [claimAt, hvis]
    obtain ⟨hj, -⟩ := visitPage_eq_some_iff.mp hvis
    have ha : startOf input j < j := startOf_lt_of_visit hv hvis
    obtain ⟨han, hmove⟩ := isTA_startOf hv hj
    rw [entryTime_startOf hv hj]
    set a := startOf input j with ha_def
    set t := entryTime input a with ht_def
    have h1 : pageDelay (snapAt input j).pending p t = pageDelay (snapAt input (a + 1)).pending p t :=
      pageDelay_of_between hv (by omega)
        (fun l' h h1 h2 => ⟨(not_tick_of_not_isTA (not_isTA_of_startOf_lt (j := j) (by omega) (by omega))
          h).1, no_visit_between hv hvis (by omega) h2⟩) t
    have h2 := pageDelay_succ_of_TA hv han hmove p
    have h3 : (snapAt input a).claims p ≤ (snapAt input j).claims p :=
      claims_le_of_between hv ha.le (fun l' h1 h2 => no_visit_before hv hvis h1 h2)
    have h4 := le_overshoot_add input (snapAt input a).pending (snapAt input a).claims t p
    have hx1 : (snapAt input j).x p ≤ 1 := ((x_frac hv j).1 p).2
    have hxδ : δ < (snapAt input j).x p := by
      obtain ⟨ρ, hρ, rfl⟩ := visit_pending hv hvis
      exact delta_lt_of_pending hv hρ
    have hc := claims_nonneg hv j p
    have ho := overshoot_nonneg (input := input) (snapAt input a).pending (snapAt input a).claims p t
    set c := (snapAt input j).claims p
    set o := overshoot input (snapAt input a).pending (snapAt input a).claims p t
    set u := (snapAt input j).x p - δ
    have hu0 : 0 ≤ u := by simp only [u]; linarith
    have hu1 : u ≤ 1 := by simp only [u]; linarith [Instance.delta_pos hv]
    calc u * pageDelay (snapAt input j).pending p t ≤ u * (c + w p + o) := by
          apply mul_le_mul_of_nonneg_left _ hu0
          rw [h1, h2]; linarith
      _ = u * c + w p * u + u * o := by ring
      _ ≤ c + w p * u + o := by
          linarith [mul_le_of_le_one_left hc hu1, mul_le_of_le_one_left ho hu1]

/-! ### Used delay -/

/-- One entry: the claim of the visited page plus the potential after the entry is at most the potential before plus `|λ|/L`. -/
theorem claimAt_add_le (i : ℕ) (h : i < (log input).length) :
    claimAt input i + ∑ q, (snapAt input (i + 1)).claims q ≤
      ∑ q, (snapAt input i).claims q + lenAt input i / L := by
  have hL := Instance.L_pos hv
  cases hvis : visitPage input i with
  | none =>
    obtain ⟨h1, h2⟩ := visitPage_eq_none hvis h
    rw [claims_succ_of_not_visit hv h h1 h2]
    simp only [claimAt, hvis, zero_add, le_add_iff_nonneg_right]
    exact div_nonneg (lenAt_nonneg i) hL.le
  | some p =>
    simp only [claimAt, hvis]
    obtain ⟨h', hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
    · rw [(critical_spec hv h hm).2.2, lenAt_of_critical h hm]
      try dsimp only
      rw [sum_update_eq (Finset.mem_univ p)]
      have hsum := sum_claimUpdate_of_triggered hv (critical_facts hv h hm).1
      rw [Finset.sum_sub_distrib] at hsum
      have hle := le_claimUpdate hv (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p p
      linarith
    · rw [(trip_spec hv h hm).2.2.2]
      try dsimp only
      rw [sum_update_eq (Finset.mem_univ π.page)]
      have := lenAt_nonneg (input := input) i
      have := div_nonneg this hL.le
      linarith

/-- **Used delay**: the claims of all visits sum to at most `∑_λ |λ| / L`. -/
theorem sum_claimAt_le :
    ∑ j ∈ Finset.range (log input).length, claimAt input j ≤ lenTotal input / L := by
  set Φ : ℕ → ℝ := fun i => ∑ q, (snapAt input i).claims q with hΦ
  have key : ∀ i ∈ Finset.range (log input).length,
      claimAt input i ≤ (Φ i - Φ (i + 1)) + lenAt input i / L := by
    intro i hi
    have := claimAt_add_le hv i (Finset.mem_range.mp hi)
    simp only [hΦ]
    linarith
  have h0 : Φ 0 = 0 := by simp [hΦ, snapAt_zero hv, initialSnap]
  have hn : 0 ≤ Φ (log input).length :=
    Finset.sum_nonneg fun q _ => claims_nonneg hv _ q
  calc _ ≤ ∑ i ∈ Finset.range (log input).length, ((Φ i - Φ (i + 1)) + lenAt input i / L) :=
        Finset.sum_le_sum key
    _ = (Φ 0 - Φ (log input).length) + lenTotal input / L := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.sum_div]
        rfl
    _ ≤ lenTotal input / L := by linarith

end

end

end PagingWithDelay.PMD.DelayProof
end

/-! ## Inlined from `PagingWithDelay.Analysis.AlgDelay.Overshoot` -/
section

/-!
# `prop:algdelay`, part 4: the overshoots

Fix a time `t`, with start index `a` (the tick or advance that set `t`), and let `F_a` be the entries at time `t` (`startOf l = a`). Let `q` be the heaviest page visited at time `t` with positive overshoot `ō_q`. Every page is visited at most once at time `t`, and `q` has not triggered since the previous time, so (`sum_overshoot_le_of_not_triggered`)

  `∑_{visits at t} ō_p ≤ ∑_{w_{q'} ≤ w_q} o_{q'}(t) ≤ |λ_q(x̄)| / L`,

with `x̄` the state at `a`. By `lem:drop` (along the chain of critical services at time `t`) and, if `q` is visited by a round trip of a level-`W` preemptive service, by its condition (`|λ_q| ≤ L W` from its start state, and `W ≤ 2 W (1 - δ)`),

  `|λ_q(x̄)| ≤ 2 ∑_{l ∈ F_a} |λ_l| + 2 L ∑_{l ∈ F_a} hole_l` (`serviceEnd_le_block`).

As in the paper, in the critical case both the chain and the service on `q` are bounded by `∑_{l ∈ F_a} |λ_l|` separately, and `L ≥ 1` turns `2/L` into `2`. Summing over the times (the `F_a` partition the entries): `∑_visits ō ≤ 2 ∑_λ |λ| + 2 · (total hole payments)` (`sum_overAt_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

variable (input) in
/-- The entries at the time started by entry `a`. -/
def block (a : ℕ) : Finset ℕ :=
  (Finset.range (log input).length).filter fun l => startOf input l = a

section

variable (hv : input.Valid)
include hv

theorem mem_block_of_between {a js l : ℕ} (hjs : js < (log input).length)
    (hja : startOf input js = a) (h1 : a ≤ l) (h2 : l ≤ js) : l ∈ block input a := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  rw [startOf_of_between hv hjs (hja ▸ h1) h2, hja]

/-- **Comparing `|λ_q(x̄)|` with the costs at time `t`**: for a visit `js` of `q` at the time started by `a`, the critical service on `q` from the state at `a` is at most twice the total length of the critical services at time `t` plus `2 L` times the hole payments at time `t`. -/
theorem serviceEnd_le_block {a js : ℕ} {q : Page} (hjs : js < (log input).length)
    (hvis : visitPage input js = some q) (hja : startOf input js = a)
    (hδ : δ < (snapAt input a).x q) :
    serviceEnd input (snapAt input a).x q ≤
      2 * ∑ l ∈ block input a, lenAt input l + 2 * L * ∑ l ∈ block input a, holeAt input l := by
  have has : a < js := hja ▸ startOf_lt_of_visit hv hvis
  obtain ⟨han, hmove⟩ : IsTA input a := hja ▸ isTA_startOf hv hjs
  have hidle : (snapAt input a).stage = .idle := by
    rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact (tick_spec hv han ht).1
    · exact (advance_spec hv han ht).1
  have hxa : (snapAt input a).x = baseState (snapAt input a) :=
    x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
  have hvb := hv
  have hrest : IsRest input (baseState (snapAt input a)) := baseState_isRest hv a
  have hδ' : δ < baseState (snapAt input a) q := by
    rw [← hxa]; exact hδ
  have hL := Instance.L_pos hv
  have hnocrit : ∀ m, m ≤ js → ∀ l (hl : l < (log input).length), a ≤ l → l < m →
      moveAt l hl ≠ .critical q := fun m hm l hl h1 h2 hc =>
    no_visit_before hv hvis (hja ▸ h1) (by omega) (visitPage_of_critical hl hc)
  have hlenF : ∀ m, m ≤ js + 1 →
      ∑ l ∈ Finset.Ico a m, lenAt input l ≤ ∑ l ∈ block input a, lenAt input l := by
    intro m hm
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      rw [Finset.mem_Ico] at hl
      exact mem_block_of_between hv hjs hja hl.1 (by omega)
    · intro l _ _; exact lenAt_nonneg l
  have hholeF : 0 ≤ ∑ l ∈ block input a, holeAt input l :=
    Finset.sum_nonneg fun l _ => holeAt_nonneg hv l
  have hlenF0 : 0 ≤ ∑ l ∈ block input a, lenAt input l :=
    Finset.sum_nonneg fun l _ => lenAt_nonneg l
  rw [hxa]
  obtain ⟨hjsn, hm | ⟨e, π, hm, hπ⟩⟩ := visitPage_eq_some_iff.mp hvis
  · -- `q` is visited by a critical service: the chain ends with it.
    obtain ⟨ps, hqps, hst, hlen⟩ := exists_chain hv has.le (hnocrit js le_rfl)
    have h1 := serviceEnd_le_chainLen_add hvb ps hrest hqps hδ'
    obtain ⟨hidle', -, -⟩ := critical_spec hv hjsn hm
    have hxjs : (snapAt input js).x = baseState (snapAt input js) :=
      x_eq_baseState hv (by intro e b hb; rw [hidle'] at hb; cases hb)
    rw [← hst, ← hxjs, hlen] at h1
    -- the chain and the service on `q` are each at most the lengths at time `t`
    have h2 := hlenF js (by omega)
    have h3 : lenAt input js ≤ ∑ l ∈ block input a, lenAt input l :=
      Finset.single_le_sum (fun l _ => lenAt_nonneg l)
        (mem_block_of_between hv hjsn hja has.le le_rfl)
    rw [lenAt_of_critical hjsn hm] at h3
    nlinarith
  · -- `q` is visited by a round trip of a level-`e` preemptive service opened at `o`.
    obtain ⟨o, ho, hojs, hmo, htrips⟩ := preempt_start hv hjsn (Or.inl ⟨π, hm⟩)
    have hao : a < o := by
      by_contra hle
      push_neg at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨π', hπ'⟩ := htrips a han hlt has
        rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rw [ht] at hπ' <;> cases hπ'
      · subst heq
        rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rw [ht] at hmo <;> cases hmo
    obtain ⟨ps, hqps, hst, hlen⟩ := exists_chain hv hao.le (hnocrit o hojs.le)
    have h1 := serviceEnd_le_chainLen_add hvb ps hrest hqps hδ'
    obtain ⟨hexam, hcond, -⟩ := openHole_spec hv ho hmo
    have hxo : (snapAt input o).x = baseState (snapAt input o) :=
      x_eq_baseState hv (by intro e b hb; rw [hexam] at hb; cases hb)
    have h2 := serviceEnd_le_of_preemptCondition hvb (hxo ▸ baseState_isRest hv o) q hcond
    rw [← hst, ← hxo, hlen] at h1
    have h3 := hlenF o (by omega)
    have hhole : holeAt input o = holePayment input e := holeAt_of_openHole ho hmo
    have hδ3 := Instance.delta_le_third hv
    have hlw : levelWeight e ≤ 2 * holeAt input o := by
      rw [hhole]
      unfold holePayment
      nlinarith [PagingWithDelay.PMD.levelWeight_pos e]
    have hoF : holeAt input o ≤ ∑ l ∈ block input a, holeAt input l :=
      Finset.single_le_sum (fun l _ => holeAt_nonneg hv l)
        (mem_block_of_between hv hjsn hja hao.le hojs.le)
    nlinarith

/-- **The overshoots at one time**: the overshoots of the visits at the time started by `a` are at most `∑_{l ∈ F_a} (2 |λ_l| + 2 hole_l)`. -/
theorem sum_overAt_block_le (a : ℕ) :
    ∑ j ∈ block input a, overAt input j ≤
      ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) := by
  have hL := Instance.L_pos hv
  have hRnn : 0 ≤ ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) :=
    Finset.sum_nonneg fun l _ =>
      add_nonneg (mul_nonneg two_pos.le (lenAt_nonneg l)) (mul_nonneg two_pos.le (holeAt_nonneg hv l))
  set G := (block input a).filter fun j => 0 < overAt input j with hG
  have hFG : ∑ j ∈ block input a, overAt input j = ∑ j ∈ G, overAt input j :=
    (Finset.sum_filter_of_ne fun j _ hne => lt_of_le_of_ne (overAt_nonneg j) (Ne.symm hne)).symm
  rw [hFG]
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · rw [hGe, Finset.sum_empty]; exact hRnn
  obtain ⟨j0, hj0⟩ := hGne
  obtain ⟨p0, hp0⟩ : ∃ p0, visitPage input j0 = some p0 := by
    cases hvis : visitPage input j0 with
    | none =>
      have := (Finset.mem_filter.mp hj0).2
      rw [overAt_of_none hvis] at this
      exact absurd this (lt_irrefl 0)
    | some p => exact ⟨p, rfl⟩
  set pg : ℕ → Page := fun j => (visitPage input j).getD p0 with hpg
  have hGmem : ∀ j ∈ G, j < (log input).length ∧ startOf input j = a ∧
      visitPage input j = some (pg j) ∧ 0 < overAt input j := by
    intro j hj
    obtain ⟨hjF, hpos⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjn, hja⟩ := Finset.mem_filter.mp hjF
    refine ⟨Finset.mem_range.mp hjn, hja, ?_, hpos⟩
    cases hvis : visitPage input j with
    | none => rw [overAt_of_none hvis] at hpos; exact absurd hpos (lt_irrefl 0)
    | some p => simp [hpg, hvis]
  obtain ⟨js, hjs, hmax⟩ :=
    Finset.exists_max_image G (fun j => w (pg j)) ⟨j0, hj0⟩
  obtain ⟨hjsn, hjsa, hjsv, hjspos⟩ := hGmem js hjs
  set q := pg js with hq
  have has : a < js := hjsa ▸ startOf_lt_of_visit hv hjsv
  obtain ⟨han, hmove⟩ : IsTA input a := hjsa ▸ isTA_startOf hv hjsn
  set ta := entryTime input a with hta
  have hoverAt : ∀ j ∈ G, overAt input j =
      overshoot input (snapAt input a).pending (snapAt input a).claims (pg j) ta := by
    intro j hj
    obtain ⟨hjn, hja, hjv, -⟩ := hGmem j hj
    rw [overAt_of_visit hjv, entryTime_startOf hv hjn, hja]
  have hpos : (snapAt input a).claims q + w q <
      pageDelay (snapAt input a).pending q ta :=
    overshoot_pos_iff.mp (by rw [← hoverAt js hjs]; exact hjspos)
  obtain ⟨ρq, hρq, hρqp⟩ : ∃ ρ ∈ (snapAt input a).pending, ρ.page = q := by
    apply exists_pending_of_pageDelay_ne (t := ta)
    have := claims_nonneg hv a q
    have := hv.weight_pos q
    intro h0; rw [h0] at hpos; linarith
  have hδq : δ < (snapAt input a).x q := hρqp ▸ delta_lt_of_pending hv hρq
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, snapAt_zero hv] at hρq; simp [initialSnap] at hρq
    · exact h0
  have hnow : (snapAt input a).now < ta := by
    rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [hta, entryTime_tick hv han ht]
      exact now_lt_upcoming hv han.le ha0 (by rw [(tick_spec hv han ht).2.2.2.1]; simp)
    · rw [hta, (entryTime_advance hv han ht).1]; exact (entryTime_advance hv han ht).2
  have hsum := sum_overshoot_le_of_not_triggered ((inv_snapAt hv a).continuous hv) hnow
    (fun τ h1 h2 => not_triggered_before hv han hmove h1 h2 q) hpos
  have hinj : Set.InjOn pg G := by
    intro j1 hj1 j2 hj2 heq
    obtain ⟨hj1n, hj1a, hj1v, -⟩ := hGmem j1 hj1
    obtain ⟨hj2n, hj2a, hj2v, -⟩ := hGmem j2 hj2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact no_visit_between hv hj2v (by rw [hj2a, ← hj1a]; exact startOf_lt_of_visit hv hj1v)
        hlt (by rw [hj1v, heq])
    · exact no_visit_between hv hj1v (by rw [hj1a, ← hj2a]; exact startOf_lt_of_visit hv hj2v)
        hlt (by rw [hj2v, heq])
  have hle1 : ∑ j ∈ G, overAt input j ≤
      ∑ p ∈ lighter input q, overshoot input (snapAt input a).pending (snapAt input a).claims p ta := by
    rw [Finset.sum_congr rfl hoverAt, ← Finset.sum_image (f := fun p =>
      overshoot input (snapAt input a).pending (snapAt input a).claims p ta) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      exact mem_lighter.mpr (hmax j hj)
    · intro _ _ _; exact overshoot_nonneg _ _ _ _
  have hblock := serviceEnd_le_block hv hjsn hjsv hjsa hδq
  have hdiv : (2 * ∑ l ∈ block input a, lenAt input l +
        2 * L * ∑ l ∈ block input a, holeAt input l) / L =
      ∑ l ∈ block input a, (2 * lenAt input l / L + 2 * holeAt input l) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
    field_simp
  calc ∑ j ∈ G, overAt input j ≤ serviceEnd input (snapAt input a).x q / L :=
        hle1.trans hsum
    _ ≤ (2 * ∑ l ∈ block input a, lenAt input l +
          2 * L * ∑ l ∈ block input a, holeAt input l) / L :=
        div_le_div_of_nonneg_right hblock hL.le
    _ = ∑ l ∈ block input a, (2 * lenAt input l / L + 2 * holeAt input l) := hdiv
    _ ≤ _ := Finset.sum_le_sum fun l _ => add_le_add_left
        (div_le_self (mul_nonneg two_pos.le (lenAt_nonneg l)) (Instance.one_le_L hv)) _

/-- **Overshoots**: the overshoots of all visits sum to at most `2 ∑_λ |λ| + 2 · (total hole payments)`. -/
theorem sum_overAt_le :
    ∑ j ∈ Finset.range (log input).length, overAt input j ≤
      2 * lenTotal input + 2 * holeTotal input := by
  have hmaps : ∀ j ∈ Finset.range (log input).length,
      startOf input j ∈ Finset.range (log input).length := fun j hj =>
    Finset.mem_range.mpr (lt_of_le_of_lt (startOf_le j) (Finset.mem_range.mp hj))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ a ∈ Finset.range (log input).length,
        ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) :=
        Finset.sum_le_sum fun a _ => sum_overAt_block_le hv a
    _ = ∑ l ∈ Finset.range (log input).length, (2 * lenAt input l + 2 * holeAt input l) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = 2 * lenTotal input + 2 * holeTotal input := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

end

end

end PagingWithDelay.PMD.DelayProof
end

/-! ## Inlined from `PagingWithDelay.Analysis.AlgDelay` -/
section

/-!
# `prop:algdelay`: the delay cost of `PMD`

**`prop:algdelay`** (`delayCost_le`): the fractional delay cost of `PMD` is at most `C_fetch + 5 ∑_λ |λ|`.

Proof, following the paper:
* `delayCost_le_sum_visitDelay` (`AlgDelay/Bridge.lean`): every request with positive fractional delay cost is pending until a visit of its page, and its weight `α_ρ` is at most `x_p - δ` right before that visit (`obs:monotone`); so the delay cost is at most `∑_visits (x_p - δ) · delay_p(t)`.
* `visitDelay_le` (`AlgDelay/Visit.lean`): a visit pays at most `c_p + (x_p - δ) w_p + ō_p`, and `(x_p - δ) w_p` is its fetch cost; the fetch costs of all visits are at most `C_fetch` (`CostProof.fetchTotal_add_tripTotal_le_fetchCost`).
* `sum_claimAt_le` (`AlgDelay/Visit.lean`): the used delays `c_p` sum to at most `∑_λ |λ| / L ≤ ∑_λ |λ|`.
* `sum_overAt_le` (`AlgDelay/Overshoot.lean`): the overshoots `ō_p` sum to at most `2 ∑_λ |λ| + 2H`, where `H` is the total payment for holes.
* `H` is paid from the budgets, so `H ≤ ∑_λ |λ|` (`CostProof.holeTotal_add_tripTotal_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

variable {input : Instance Page}

/-- **`prop:algdelay`**: the fractional delay cost of `PMD` is at most its fetch cost plus `5` times the total length of its critical services. -/
theorem delayCost_le (hv : input.Valid) :
    FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) + 5 * lenTotal input := by
  have h1 := delayCost_le_sum_visitDelay hv
  have h2 : ∑ j ∈ Finset.range (log input).length, visitDelay input j ≤
      ∑ j ∈ Finset.range (log input).length,
        (claimAt input j + (fetchAt input j + tripAt input j) + overAt input j) :=
    Finset.sum_le_sum fun j _ => visitDelay_le hv j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
  have h3 := sum_claimAt_le hv
  have h4 := sum_overAt_le hv
  have hfetch := CostProof.fetchTotal_add_tripTotal_le_fetchCost hv
  have hH := CostProof.holeTotal_add_tripTotal_le hv
  have hR := CostProof.tripTotal_nonneg hv
  have hΛ := CostProof.lenTotal_nonneg hv
  have hc : lenTotal input / L ≤ lenTotal input := div_le_self hΛ (Instance.one_le_L hv)
  unfold fetchTotal tripTotal at *
  linarith

end PagingWithDelay.PMD.DelayProof
end

/-! ## Inlined from `PagingWithDelay.Main` -/
section

/-!
# Assembling the bound

As in the paper: `prop:tele` (`fetchTotal_le_excess`, from `TeleProof.fetchTotal_le` and `lem:miss`) and `prop:excess` (`excess_le`, from `lem:timely`, the overdue part and `lem:chargeable`) bound `∑_λ fetch(λ)`; `prop:preemptfetch`, `lem:lengthfetch` (`CostProof`) and `prop:algdelay` bound the cost of the output in terms of `∑_λ fetch(λ)` (`prop:cost`, `cost_le`). Constants are those of the paper's displays; where the paper writes `O(·)`, they are those of its proof.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace MainProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

open Finset Classical

/-- The fetch cost of a schedule is nonnegative. -/
theorem costFrom_nonneg (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) :
    ∀ (C : Finset Page) (S : Schedule Page),
      0 ≤ Schedule.costFrom w C S
  | _, [] => le_rfl
  | C, step :: rest => by
    simp only [Schedule.costFrom]
    exact add_nonneg (sum_nonneg fun p _ => hw p) (costFrom_nonneg w hw _ rest)

open scoped InstanceNotation

/-- A chargeable round trip is a chargeable visit: `tripChargeW ≤ chargeW`. -/
theorem tripChargeW_le_chargeW (hv : input.Valid) {σ : Request Page → ℝ} {S : Schedule Page}
    (i : ℕ) : tripChargeW input σ S i ≤ chargeW input σ S i := by
  by_cases hi : i < (log input).length
  · simp only [tripChargeW, dif_pos hi]
    split
    · exact le_rfl
    · exact TeleProof.chargeW_nonneg hv i
  · simp only [tripChargeW, dif_neg hi]
    exact TeleProof.chargeW_nonneg hv i

/-- **`lem:miss`**: the weights of the miss services sum to at most `OPT + w(OPT₀)`. -/
theorem sum_missW_le (hv : input.Valid) {σ : Request Page → ℝ}
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    ∑ i ∈ range (log input).length, missW input S i ≤
      S.fetchCost input + Schedule.totalDelay input σ + ∑ p ∈ input.initialCache, w p := by
  have h1 : ∑ i ∈ range (log input).length, missW input S i ≤
      ∑ i ∈ range (log input).length, chargeW input σ S i :=
    sum_le_sum fun i _ => TeleProof.missW_le_chargeW hv hσ hF i
  have h2 := TeleProof.sum_chargeW_le hv hσ hSw hF
  linarith

/-- **`prop:excess`**: `Exc ≤ L · OPT + (3/2) (OPT + w(OPT₀)) + (L + 4) (OPT + w(OPT₀))`, the last display of the paper's proof. -/
theorem excess_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    ∑ i ∈ range (log input).length, excessAt input S i ≤
      L * (S.fetchCost input + Schedule.totalDelay input σ) +
        3 / 2 * (S.fetchCost input + Schedule.totalDelay input σ +
          ∑ p ∈ input.initialCache, w p) +
        (L + 4) * (S.fetchCost input + Schedule.totalDelay input σ +
          ∑ p ∈ input.initialCache, w p) := by
  have hL := Instance.one_le_L hv
  -- `lem:timely` and the overdue services
  have hnot := NotOverdueProof.sum_excess_notOverdue_le hv hσ hF
  have hover := ExcessProof.sum_excess_overdue_le hv h2 hσ hSw hF
  have hsplit : ∑ i ∈ range (log input).length, excessAt input S i =
      ∑ i ∈ range (log input).length,
          (if IsOverdue input σ S i then excessAt input S i else 0) +
        ∑ i ∈ range (log input).length,
          (if IsOverdue input σ S i then 0 else excessAt input S i) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by split_ifs <;> ring
  -- `lem:chargeable` for the chargeable round trips
  have htrip : ∑ i ∈ range (log input).length, tripChargeW input σ S i ≤
      ∑ i ∈ range (log input).length, chargeW input σ S i :=
    sum_le_sum fun i _ => tripChargeW_le_chargeW hv i
  have hcharge := TeleProof.sum_chargeW_le hv hσ hSw hF
  have hW0 : 0 ≤ ∑ p ∈ input.initialCache, w p :=
    sum_nonneg fun p _ => (hv.weight_pos p).le
  have hOd := Schedule.totalDelay_nonneg hv hσ
  have hOf : 0 ≤ S.fetchCost input :=
    costFrom_nonneg _ (fun p => (hv.weight_pos p).le) _ _
  nlinarith

/-- **`prop:tele`**: `C_fetch^crit ≤ (3L + 2) OPT + Exc + (4L + 2) ∑ wᵢ`. -/
theorem fetchTotal_le_excess (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    fetchTotal input ≤
      (3 * L + 2) * (S.fetchCost input + Schedule.totalDelay input σ) +
        ∑ i ∈ range (log input).length, excessAt input S i +
        (4 * L + 2) * input.totalWeight := by
  have hL := Instance.one_le_L hv
  have htele := TeleProof.fetchTotal_le hv hσ hSw h2
  have hmiss := sum_missW_le hv hσ hSw hF
  have hW0 : ∑ p ∈ input.initialCache, w p ≤ input.totalWeight :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => (hv.weight_pos p).le
  have hW0' : 0 ≤ ∑ p ∈ input.initialCache, w p :=
    sum_nonneg fun p _ => (hv.weight_pos p).le
  have hOd := Schedule.totalDelay_nonneg hv hσ
  have hOf : 0 ≤ S.fetchCost input :=
    costFrom_nonneg _ (fun p => (hv.weight_pos p).le) _ _
  nlinarith

/-- `prop:tele` + `prop:excess` (first display of the proof of `thm:main`): `C_fetch^crit ≤ (5L + 15/2) OPT + (5L + 15/2) ∑ wᵢ`. -/
theorem fetchTotal_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    fetchTotal input ≤
      (5 * L + 15 / 2) * (S.fetchCost input + Schedule.totalDelay input σ) +
        (5 * L + 15 / 2) * input.totalWeight := by
  have hL := Instance.one_le_L hv
  have htele := fetchTotal_le_excess hv h2 hσ hSw hF
  have hexc := excess_le hv h2 hσ hSw hF
  have hW0 : ∑ p ∈ input.initialCache, w p ≤ input.totalWeight :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => (hv.weight_pos p).le
  nlinarith

/-- **`prop:cost`**: `C_fetch + C_delay ≤ 23 C_fetch^crit + 21 ∑ wᵢ`, given `prop:algdelay`. -/
theorem cost_le (hv : input.Valid)
    (hdelay : FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) + 5 * lenTotal input) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      23 * fetchTotal input + 21 * input.totalWeight := by
  have hf := CostProof.fetchCost_le_lenTotal hv
  have hlen := CostProof.lenTotal_le_fetchTotal hv
  unfold FracSchedule.cost
  linarith

/-- **The fractional bound.** For power-of-two weights, the cost of `PMD` (fetch cost plus fractional delay cost) is `O(L)` times the cost of any feasible schedule `S` with service times `σ`. -/
theorem cost_le_costWith (input : Instance Page) (h2 : input.PowerOfTwoWeights)
    (S : Schedule Page) (σ : Request Page → ℝ) (hS : S.Feasible input)
    (hστ : S.ServiceTimes input σ) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      (115 * L + 345 / 2) * S.costWith input σ + (115 * L + 387 / 2) * input.totalWeight := by
  have hv := input.valid
  have hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ := fun ρ hρ => (hστ ρ hρ).1
  obtain ⟨S', hF', hSw', hc'⟩ := Schedule.exists_swapForm hv hS hστ
  have hL := Instance.one_le_L hv
  have hT := Instance.totalWeight_nonneg hv
  have hfe := fetchTotal_le hv h2 hσ hSw' hF'
  have hcost : S'.fetchCost input + Schedule.totalDelay input σ ≤ S.costWith input σ := by
    rw [Schedule.costWith_eq]; linarith
  have hfe' : fetchTotal input ≤
      (5 * L + 15 / 2) * S.costWith input σ + (5 * L + 15 / 2) * input.totalWeight := by
    have := mul_le_mul_of_nonneg_left hcost (by linarith : (0 : ℝ) ≤ 5 * L + 15 / 2)
    linarith
  have := cost_le hv (DelayProof.delayCost_le hv)
  nlinarith

/-- **The fractional bound**, against the cost of `S` with its first service times. -/
theorem fracCost_le (input : Instance Page) (h2 : input.PowerOfTwoWeights)
    (S : Schedule Page) (hS : S.Feasible input) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      (115 * L + 345 / 2) * S.cost input + (115 * L + 387 / 2) * input.totalWeight := by
  rw [Schedule.cost_eq_costWith]
  exact cost_le_costWith input h2 S _ hS (Schedule.serviceTimes_serviceTime hS)

end MainProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Rounded` -/
section

/-!
# Arbitrary weights: rounding up to powers of two

The first step of the proof of `thm:main`: rounding every weight up to a power of two (`w ↦ 2^⌈log₂ w⌉ ∈ [w, 2w)`) at most doubles the cost of every schedule and does not decrease it.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open scoped InstanceNotation in
/-- The instance with every weight rounded up to a power of two, `w ↦ 2^⌈log₂ w⌉`. -/
noncomputable def Instance.roundWeights (input : Instance Page) : Instance Page :=
  { input with
    weight := fun p => (2 : ℝ) ^ Int.clog 2 (w p)
    weight_pos := fun p => by positivity }

namespace Schedule

theorem costFrom_mono {w w' : Page → ℝ} (hw : ∀ p, w p ≤ w' p) :
    ∀ (C : Finset Page) (S : Schedule Page), costFrom w C S ≤ costFrom w' C S
  | _, [] => le_rfl
  | C, step :: rest => by
      simp only [costFrom]
      exact add_le_add (Finset.sum_le_sum fun p _ => hw p) (costFrom_mono hw step.cache rest)

theorem costFrom_smul (w : Page → ℝ) (a : ℝ) :
    ∀ (C : Finset Page) (S : Schedule Page),
      costFrom (fun p => a * w p) C S = a * costFrom w C S
  | _, [] => by simp [costFrom]
  | C, step :: rest => by
      simp only [costFrom, costFrom_smul w a step.cache rest, mul_add, Finset.mul_sum]

end Schedule

open scoped InstanceNotation

namespace PMD

namespace RoundedProof

variable {input : Instance Page}

open Finset

theorem roundWeights_powerOfTwo : input.roundWeights.PowerOfTwoWeights :=
  fun p => ⟨Int.clog 2 (w p), rfl⟩

theorem le_roundWeights (p : Page) : w p ≤ input.roundWeights.weight p := by
  have := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) (w p)
  simpa [Instance.roundWeights] using this

theorem roundWeights_le (p : Page) : input.roundWeights.weight p ≤ 2 * w p := by
  have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) (input.weight_pos p)
  simp only [Instance.roundWeights]
  have : (2 : ℝ) ^ Int.clog 2 (w p) =
      2 * (2 : ℝ) ^ (Int.clog 2 (w p) - 1) := by
    rw [← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
  push_cast at h
  rw [this]; linarith

theorem roundWeights_L : input.roundWeights.L = L := rfl

theorem roundWeights_upTo (t : ℝ) : (input.upTo t).roundWeights = input.roundWeights.upTo t :=
  rfl

theorem totalWeight_roundWeights_le :
    input.roundWeights.totalWeight ≤ 2 * input.totalWeight := by
  unfold Instance.totalWeight
  rw [mul_sum]
  exact sum_le_sum fun p _ => roundWeights_le p

theorem feasible_roundWeights_iff {S : Schedule Page} :
    S.Feasible input.roundWeights ↔ S.Feasible input :=
  ⟨fun h => ⟨h.chronological, h.capacity, h.serves⟩,
    fun h => ⟨h.chronological, h.capacity, h.serves⟩⟩

/-- The cost of a schedule with the original weights is at most its cost with the rounded weights (the delay costs agree). -/
theorem cost_le_cost_roundWeights (S : Schedule Page) :
    S.cost input ≤ S.cost input.roundWeights := by
  unfold Schedule.cost Schedule.fetchCost
  have := Schedule.costFrom_mono (fun p => le_roundWeights (input := input) p)
    input.initialCache S
  exact add_le_add this le_rfl

/-- Rounding the weights at most doubles the cost of a schedule. -/
theorem cost_roundWeights_le (S : Schedule Page) (hS : S.Feasible input) :
    S.cost input.roundWeights ≤ 2 * S.cost input := by
  have hv := input.valid
  have hf : S.fetchCost input.roundWeights ≤ 2 * S.fetchCost input := by
    unfold Schedule.fetchCost
    rw [← Schedule.costFrom_smul]
    exact Schedule.costFrom_mono (fun p => roundWeights_le p) _ _
  have hσ := Schedule.serviceTimes_serviceTime hS
  have hd := Schedule.totalDelay_nonneg hv (fun ρ hρ => (hσ ρ hρ).1)
  have he : S.cost input.roundWeights = S.fetchCost input.roundWeights +
      Schedule.totalDelay input (S.serviceTime input) := rfl
  rw [he, Schedule.cost_eq_costWith, Schedule.costWith_eq]
  linarith

end RoundedProof

end PMD

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.BBNDefs` -/
section

/-!
# Notation for the online rounding theorem for weighted paging

The only result that this formalization assumes without proof: the online rounding theorem of Bansal, Buchbinder and Naor for weighted paging (*A primal-dual randomized algorithm for weighted paging*, Theorem 4.1), in the form and notation in which the appendix "Rounding" of the paper restates it (with `Q'`, `y'` for the paper's `Q̃`, `ỹ`).

* A *cache state* is a set of `k` pages. `Q`, `Q'` are probability distributions on sets of pages (`PMF (Finset Page)`) that give positive probability only to cache states.
* `𝒫` (`fracCaches k`): the *distributions on pages* `y ∈ [0,1]ⁿ` with `∑ᵢ yᵢ = k`; `yᵢ` is the cached mass of page `i`.
* `Π(Q)` (`marginal Q`): `Π(Q)ᵢ` is the probability that page `i` is in the random cache with distribution `Q`.
* A *transition* from `Q` to `Q'` is a joint distribution `π` of the cache `C` before and the cache `C'` after it, with marginals `Q` and `Q'`. Its expected cost (`transitionCost`) charges `wᵢ/2` for every fetched page `i ∈ C' \ C` and for every evicted page `i ∈ C \ C'`. `cost(Q, Q')` is the minimum of this over all transitions; it is attained (a linear program over a compact set), so `cost(Q, Q') ≤ c` says that some transition costs at most `c`.
* `cost_f(y, y') = ∑ᵢ (wᵢ/2) |yᵢ - y'ᵢ|` (`fracCost`).

Besides the statement of Theorem 4.1, the paper uses (in the proof of the online rounding corollary in the appendix "Rounding", citing the proof of Theorem 4.1) that `𝒟` contains a distribution whose marginals are the indicator vector of the initial cache. The only such distribution on cache states is the one concentrated on the initial cache, so we assume: `𝒟` contains the distribution concentrated on any single cache state.
-/

namespace PagingWithDelay

namespace BBN

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- `𝒫`: the fractional caches `y ∈ [0,1]ⁿ` with total cached mass `∑ᵢ yᵢ = k`. -/
def fracCaches (k : ℕ) : Set (Page → ℝ) :=
  {y | (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = k}

/-- `Q` is a distribution on cache states: every set of pages that it gives positive probability has exactly `k` pages. -/
def OnCacheStates (k : ℕ) (Q : PMF (Finset Page)) : Prop :=
  ∀ C ∈ Q.support, C.card = k

/-- The marginals `Π(Q)ᵢ = Pr_{C ∼ Q}[i ∈ C]`. -/
noncomputable def marginal (Q : PMF (Finset Page)) (i : Page) : ℝ :=
  ∑ C : Finset Page, if i ∈ C then (Q C).toReal else 0

/-- The expected cost of the transition `π` (a joint distribution of the cache `C` before and the cache `C'` after it): `wᵢ/2` for every fetched page `i ∈ C' \ C` and for every evicted page `i ∈ C \ C'`. -/
noncomputable def transitionCost (w : Page → ℝ) (π : PMF (Finset Page × Finset Page)) : ℝ :=
  ∑ CC : Finset Page × Finset Page,
    (π CC).toReal * ((∑ i ∈ CC.2 \ CC.1, w i / 2) + ∑ i ∈ CC.1 \ CC.2, w i / 2)

/-- `cost_f(y, y') = ∑ᵢ (wᵢ/2) |yᵢ - y'ᵢ|`. -/
noncomputable def fracCost (w : Page → ℝ) (y y' : Page → ℝ) : ℝ :=
  ∑ i, w i / 2 * |y i - y' i|

end BBN

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Rounding.Map` -/
section

set_option linter.unusedSectionVars false

/-!
# The rounding map (`lem:map`) and the lazy fractional caches

The fractional states `x ∈ [δ, 1]ⁿ` of `PMD` (missing masses, `∑ᵢ xᵢ ≥ n - k`, `δ = 1/(2k+1)`) are turned into fractional caches for `cor:rounding`:
* `zmap δ x`: `zᵢ = max 0 (2 uᵢ - 1)` with `uᵢ = (1 - xᵢ)/(1 - δ)` (`lem:map`), a cached mass in `[0,1]` with `zᵢ = 1` if `xᵢ = δ`, total `≤ k`;
* `lazySeq k zs`: the lazy fractional caches `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾` of total mass exactly `k`; `y⁽⁰⁾ = z⁽⁰⁾`, and `y⁽ᵛ⁺¹⁾ = lazyStep k y⁽ᵛ⁾ z⁽ᵛ⁺¹⁾` raises each `yᵢ` to `max yᵢ z'ᵢ`, then lowers the excess over `z'` by a common fraction until the total is `k`.
-/

namespace PagingWithDelay

namespace Rounding

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The rounding map of `lem:map`: `zᵢ = max 0 (2 (1 - xᵢ)/(1 - δ) - 1)`. -/
noncomputable def zmap (δ : ℝ) (x : Page → ℝ) : Page → ℝ :=
  fun i => max 0 (2 * ((1 - x i) / (1 - δ)) - 1)

/-- One lazy step: raise `y` to `max y z`, then lower the excess `max y z - z` by a common fraction so that the total is `k`. -/
noncomputable def lazyStep (k : ℕ) (y z : Page → ℝ) : Page → ℝ :=
  fun i => z i + ((k - ∑ j, z j) / ∑ j, (max (y j) (z j) - z j)) * (max (y i) (z i) - z i)

/-- The lazy sequence: `y⁽⁰⁾ = z⁽⁰⁾`, `y⁽ᵛ⁺¹⁾ = lazyStep k y⁽ᵛ⁾ z⁽ᵛ⁺¹⁾`. -/
noncomputable def lazySeq (k : ℕ) : List (Page → ℝ) → List (Page → ℝ)
  | [] => []
  | z :: zs => z :: lazyFrom k z zs
where
  /-- The lazy caches after `y` for the targets `zs`. -/
  lazyFrom (k : ℕ) (y : Page → ℝ) : List (Page → ℝ) → List (Page → ℝ)
    | [] => []
    | z :: zs => lazyStep k y z :: lazyFrom k (lazyStep k y z) zs

/-! ## `lem:map` -/

variable {k : ℕ} {δ : ℝ}

/-- With `δ = 1/(2k+1)` and `k ≥ 1`: `0 < δ`, `1 - δ ≥ 2/3` and `k = (k + 1/2)(1 - δ)`. -/
lemma delta_facts (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) :
    0 < δ ∧ 2 / 3 ≤ 1 - δ ∧ (k : ℝ) = (k + 1 / 2) * (1 - δ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * k + 1 := by linarith
  subst hδ
  refine ⟨by positivity, ?_, ?_⟩
  · rw [le_sub_iff_add_le, div_add_div _ _ (by norm_num) hpos.ne', div_le_one (by positivity)]
    nlinarith
  · field_simp
    ring

/-- Unfolding `zmap`. -/
lemma zmap_apply (x : Page → ℝ) (i : Page) :
    zmap δ x i = max 0 (2 * ((1 - x i) / (1 - δ)) - 1) := rfl

theorem zmap_mem_fracCaches_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ}
    (hx : ∀ i, δ ≤ x i ∧ x i ≤ 1) (hmass : (Fintype.card Page : ℝ) - k ≤ ∑ i, x i) :
    (∀ i, 0 ≤ zmap δ x i ∧ zmap δ x i ≤ 1) ∧ ∑ i, zmap δ x i ≤ k := by
  obtain ⟨hδ0, hδ1, hkδ⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  set u : Page → ℝ := fun i => (1 - x i) / (1 - δ) with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => div_nonneg (by linarith [(hx i).2]) hc.le
  have hu1 : ∀ i, u i ≤ 1 := fun i => (div_le_one hc).2 (by linarith [(hx i).1])
  have hz : ∀ i, zmap δ x i = max 0 (2 * u i - 1) := fun i => rfl
  refine ⟨fun i => ⟨by rw [hz]; exact le_max_left _ _, by
    rw [hz]; exact max_le (by norm_num) (by linarith [hu1 i])⟩, ?_⟩
  -- `∑ u ≤ k + 1/2`
  have hsumu : ∑ i, u i ≤ k + 1 / 2 := by
    have : ∑ i, u i = (Fintype.card Page - ∑ i, x i) / (1 - δ) := by
      simp only [hu, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [this, div_le_iff₀ hc]
    linarith
  -- only the pages in `A = {i | uᵢ > 1/2}` contribute
  set A := Finset.univ.filter (fun i => 1 / 2 < u i) with hA
  have hsumA : ∑ i, zmap δ x i = ∑ i ∈ A, (2 * u i - 1) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz]
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  have h1 : ∑ i ∈ A, (2 * u i - 1) ≤ A.card := by
    rw [← mul_one (A.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => by linarith [hu1 i]
  have h2 : ∑ i ∈ A, (2 * u i - 1) ≤ 2 * (k + 1 / 2) - A.card := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ∑ i ∈ A, u i ≤ ∑ i, u i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hu0 i
    linarith
  rw [hsumA]
  rcases le_or_gt A.card k with h | h
  · exact h1.trans (by exact_mod_cast h)
  · have : (k : ℝ) + 1 ≤ A.card := by exact_mod_cast h
    linarith

theorem zmap_eq_one (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ} {i : Page}
    (hi : x i = δ) : zmap δ x i = 1 := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  rw [zmap_apply, hi, div_self (by linarith)]
  norm_num

/-- `1 - zᵢ ≤ 3 (xᵢ - δ)`: the probability that page `i` is not cached. -/
theorem one_sub_zmap_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ} {i : Page}
    (hi : δ ≤ x i) : 1 - zmap δ x i ≤ 3 * (x i - δ) := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  have : 1 - (2 * ((1 - x i) / (1 - δ)) - 1) ≤ 3 * (x i - δ) := by
    have e : 1 - (2 * ((1 - x i) / (1 - δ)) - 1) = 2 * (x i - δ) / (1 - δ) := by
      field_simp
      ring
    rw [e, div_le_iff₀ hc]
    nlinarith
  linarith [le_max_right 0 (2 * ((1 - x i) / (1 - δ)) - 1), zmap_apply (δ := δ) x i]

/-- `z` is nonincreasing and `3`-Lipschitz in each coordinate: `(z(x')ᵢ - z(x)ᵢ)⁺ ≤ 3 (xᵢ - x'ᵢ)⁺`. -/
theorem zmap_sub_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) (x x' : Page → ℝ) (i : Page) :
    max 0 (zmap δ x' i - zmap δ x i) ≤ 3 * max 0 (x i - x' i) := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  set a := 2 * ((1 - x i) / (1 - δ)) - 1
  set a' := 2 * ((1 - x' i) / (1 - δ)) - 1
  have e : a' - a = 2 * (x i - x' i) / (1 - δ) := by
    simp only [a, a']
    field_simp
    ring
  have hle : max 0 a' - max 0 a ≤ max 0 (a' - a) := by
    simpa using max_sub_max_le_max 0 a' 0 a
  have hd : max 0 (a' - a) ≤ 3 * max 0 (x i - x' i) := by
    apply max_le (by positivity)
    rw [e, div_le_iff₀ hc]
    rcases le_total 0 (x i - x' i) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  exact max_le (by positivity) (hle.trans hd)

/-! ## The lazy sequence -/

/-- One lazy step keeps the invariant: for `y ∈ 𝒫` and `z ∈ [0,1]ⁿ` with `∑ z ≤ k`, `y' = lazyStep k y z` satisfies `z ≤ y' ≤ max y z` and `y' ∈ 𝒫`. -/
theorem lazyStep_spec {y z : Page → ℝ} (hy : y ∈ BBN.fracCaches k)
    (hz : (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k) :
    (∀ i, z i ≤ lazyStep k y z i ∧ lazyStep k y z i ≤ max (y i) (z i)) ∧
      lazyStep k y z ∈ BBN.fracCaches k := by
  obtain ⟨hy01, hysum⟩ := hy
  obtain ⟨hz01, hzsum⟩ := hz
  set S := ∑ j, (max (y j) (z j) - z j) with hS
  have hd : ∀ j, 0 ≤ max (y j) (z j) - z j := fun j => by linarith [le_max_right (y j) (z j)]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hd j
  have hDS : (k : ℝ) - ∑ j, z j ≤ S := by
    have : ∑ j, y j ≤ ∑ j, max (y j) (z j) := Finset.sum_le_sum fun j _ => le_max_left _ _
    rw [hS, Finset.sum_sub_distrib]
    linarith
  set θ := ((k : ℝ) - ∑ j, z j) / S with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hS0
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ hDS hS0
  have hy' : ∀ i, lazyStep k y z i = z i + θ * (max (y i) (z i) - z i) := fun i => rfl
  have hbd : ∀ i, z i ≤ lazyStep k y z i ∧ lazyStep k y z i ≤ max (y i) (z i) := fun i => by
    rw [hy']
    constructor
    · nlinarith [hd i]
    · nlinarith [hd i]
  refine ⟨hbd, fun i => ⟨(hz01 i).1.trans (hbd i).1,
    (hbd i).2.trans (max_le (hy01 i).2 (hz01 i).2)⟩, ?_⟩
  simp only [hy', Finset.sum_add_distrib, ← Finset.mul_sum]
  rcases hS0.lt_or_eq with h | h
  · rw [hθ, div_mul_cancel₀ _ h.ne']
    ring
  · rw [← hS, ← h, mul_zero, add_zero]
    linarith

/-- The lazy sequence as a scan: `lazySeq k (z :: zs) = scanl (lazyStep k) z zs`. -/
theorem lazySeq_cons (z : Page → ℝ) (zs : List (Page → ℝ)) :
    lazySeq k (z :: zs) = List.scanl (lazyStep k) z zs := by
  suffices h : ∀ (y : Page → ℝ) (zs : List (Page → ℝ)),
      y :: lazySeq.lazyFrom k y zs = List.scanl (lazyStep k) y zs from h z zs
  intro y zs
  induction zs generalizing y with
  | nil => simp [lazySeq.lazyFrom]
  | cons z zs ih => simp [lazySeq.lazyFrom, ih, List.scanl_cons]

theorem length_lazySeq (zs : List (Page → ℝ)) : (lazySeq k zs).length = zs.length := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq_cons]

/-- The lazy sequence is computed online. -/
theorem lazySeq_take (zs : List (Page → ℝ)) (m : ℕ) :
    (lazySeq k zs).take m = lazySeq k (zs.take m) := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs =>
    cases m with
    | zero => simp [lazySeq]
    | succ m => simp [lazySeq_cons, List.take_scanl]

theorem head?_lazySeq (zs : List (Page → ℝ)) : (lazySeq k zs).head? = zs.head? := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq]

/-- The recursion of the lazy sequence by index (with default `0` out of range). -/
theorem getD_lazySeq_succ {zs : List (Page → ℝ)} {ν : ℕ} (hν : ν + 1 < zs.length) :
    (lazySeq k zs).getD (ν + 1) 0 = lazyStep k ((lazySeq k zs).getD ν 0) (zs.getD (ν + 1) 0) := by
  cases zs with
  | nil => simp at hν
  | cons z zs =>
    simp only [List.length_cons] at hν
    rw [lazySeq_cons, List.getD_eq_getElem _ _ (by simpa using hν),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_succ_scanl]
    have : ν < zs.length := by omega
    simp [this]

theorem getD_lazySeq_zero (zs : List (Page → ℝ)) : (lazySeq k zs).getD 0 0 = zs.getD 0 0 := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq]

/-- The invariant of the lazy sequence, by index: `y⁽ᵛ⁾ ∈ 𝒫` and `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾`. -/
theorem getD_lazySeq_spec {zs : List (Page → ℝ)}
    (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) (ν : ℕ) (hν : ν < zs.length) :
    (lazySeq k zs).getD ν 0 ∈ BBN.fracCaches k ∧
      ∀ i, zs.getD ν 0 i ≤ (lazySeq k zs).getD ν 0 i := by
  have hzν : ∀ ν (hν : ν < zs.length), (∀ i, 0 ≤ zs.getD ν 0 i ∧ zs.getD ν 0 i ≤ 1) ∧
      ∑ i, zs.getD ν 0 i ≤ k := fun ν hν => by
    rw [List.getD_eq_getElem _ _ hν]; exact hz _ (List.getElem_mem hν)
  induction ν with
  | zero =>
    rw [getD_lazySeq_zero]
    refine ⟨⟨(hzν 0 hν).1, ?_⟩, fun i => le_rfl⟩
    cases zs with
    | nil => simp at hν
    | cons z zs => simpa using h0 z (by simp)
  | succ ν ih =>
    rw [getD_lazySeq_succ hν]
    obtain ⟨h1, h2⟩ := lazyStep_spec (ih (by omega)).1 (hzν _ hν)
    exact ⟨h2, fun i => (h1 i).1⟩

/-- The lazy caches dominate the targets: `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾`. -/
theorem le_lazySeq {zs : List (Page → ℝ)} (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) (ν : ℕ) (hν : ν < (lazySeq k zs).length) (i : Page) :
    (zs[ν]'(by simpa [length_lazySeq] using hν)) i ≤ (lazySeq k zs)[ν] i := by
  have hν' : ν < zs.length := by simpa [length_lazySeq] using hν
  have := (getD_lazySeq_spec hz h0 ν hν').2 i
  rwa [List.getD_eq_getElem _ _ hν, List.getD_eq_getElem _ _ hν'] at this

theorem lazySeq_mem {zs : List (Page → ℝ)} (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) : ∀ y ∈ lazySeq k zs, y ∈ BBN.fracCaches k := by
  intro y hy
  obtain ⟨ν, hν, rfl⟩ := List.getElem_of_mem hy
  have hν' : ν < zs.length := by simpa [length_lazySeq] using hν
  have := (getD_lazySeq_spec hz h0 ν hν').1
  rwa [List.getD_eq_getElem _ _ hν] at this

/-- `|a| = 2 a⁺ - a`. -/
lemma abs_eq_two_mul_max_sub (a : ℝ) : |a| = 2 * max 0 a - a := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_right h]; ring
  · rw [abs_of_nonpos h, max_eq_left h]; ring

/-- Per page: the total movement of a sequence `a` in `[0,1]` whose increments are bounded by the positive increments of `b` is at most `2 ∑ (Δb)⁺ + 1`. -/
lemma sum_abs_sub_le (a b : ℕ → ℝ) (N : ℕ) (ha : ∀ ν, 0 ≤ a ν ∧ a ν ≤ 1)
    (hab : ∀ ν < N, a (ν + 1) - a ν ≤ max 0 (b (ν + 1) - b ν)) :
    ∑ ν ∈ Finset.range N, |a (ν + 1) - a ν| ≤
      2 * ∑ ν ∈ Finset.range N, max 0 (b (ν + 1) - b ν) + 1 := by
  simp only [abs_eq_two_mul_max_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (f := a)]
  have : ∑ ν ∈ Finset.range N, max 0 (a (ν + 1) - a ν) ≤
      ∑ ν ∈ Finset.range N, max 0 (b (ν + 1) - b ν) :=
    Finset.sum_le_sum fun ν hν =>
      max_le (le_max_left _ _) (hab ν (Finset.mem_range.1 hν))
  linarith [(ha N).1, (ha 0).2]

/-- The movement cost of the lazy caches: `∑ᵥ ∑ᵢ wᵢ |y⁽ᵛ⁺¹⁾ᵢ - y⁽ᵛ⁾ᵢ| ≤ 2 ∑ᵥ ∑ᵢ wᵢ (z⁽ᵛ⁺¹⁾ᵢ - z⁽ᵛ⁾ᵢ)⁺ + ∑ᵢ wᵢ`. -/
theorem sum_movement_lazySeq_le (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) {zs : List (Page → ℝ)}
    (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) :
    ∑ ν ∈ Finset.range (zs.length - 1),
        ∑ i, w i * |(lazySeq k zs).getD (ν + 1) 0 i - (lazySeq k zs).getD ν 0 i| ≤
      2 * ∑ ν ∈ Finset.range (zs.length - 1),
          ∑ i, w i * max 0 (zs.getD (ν + 1) 0 i - zs.getD ν 0 i) + ∑ i, w i := by
  set Y := fun ν => (lazySeq k zs).getD ν 0 with hY
  set Z := fun ν => zs.getD ν 0 with hZ
  -- every `y⁽ᵛ⁾` lies in `[0,1]ⁿ` (the default `0` too)
  have hY01 : ∀ ν i, 0 ≤ Y ν i ∧ Y ν i ≤ 1 := fun ν i => by
    rcases lt_or_ge ν zs.length with h | h
    · exact (getD_lazySeq_spec hz h0 ν h).1.1 i
    · have h' : (lazySeq k zs).length ≤ ν := by rwa [length_lazySeq]
      simp only [hY]
      rw [List.getD_eq_default _ _ h']
      simp
  -- `y⁽ᵛ⁺¹⁾ᵢ - y⁽ᵛ⁾ᵢ ≤ (z⁽ᵛ⁺¹⁾ᵢ - z⁽ᵛ⁾ᵢ)⁺`
  have hstep : ∀ i, ∀ ν < zs.length - 1,
      Y (ν + 1) i - Y ν i ≤ max 0 (Z (ν + 1) i - Z ν i) := fun i ν hν => by
    have hν1 : ν + 1 < zs.length := by omega
    obtain ⟨hYν, hZY⟩ := getD_lazySeq_spec hz h0 ν (by omega)
    have hZ1 : (∀ i, 0 ≤ Z (ν + 1) i ∧ Z (ν + 1) i ≤ 1) ∧ ∑ i, Z (ν + 1) i ≤ k := by
      simp only [hZ, List.getD_eq_getElem _ _ hν1]; exact hz _ (List.getElem_mem hν1)
    have h := ((lazyStep_spec hYν hZ1).1 i).2
    simp only [hY] at h ⊢
    rw [getD_lazySeq_succ hν1]
    have := hZY i
    simp only [hZ] at hZ1 ⊢
    rcases le_total (Y ν i) (Z (ν + 1) i) with h' | h'
    · simp only [hY, hZ] at h'
      rw [max_eq_right h'] at h
      exact le_max_of_le_right (by linarith)
    · simp only [hY, hZ] at h'
      rw [max_eq_left h'] at h
      exact le_max_of_le_left (by linarith)
  calc ∑ ν ∈ Finset.range (zs.length - 1), ∑ i, w i * |Y (ν + 1) i - Y ν i|
      = ∑ i, w i * ∑ ν ∈ Finset.range (zs.length - 1), |Y (ν + 1) i - Y ν i| := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ i, w i * (2 * ∑ ν ∈ Finset.range (zs.length - 1), max 0 (Z (ν + 1) i - Z ν i) + 1) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (sum_abs_sub_le (fun ν => Y ν i) (fun ν => Z ν i) _ (hY01 · i) (hstep i)) (hw i)
    _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ => by ring

end Rounding

end PagingWithDelay
end

/-! ## Inlined from `PagingWithDelay.Rounding.Core` -/
section

/-!
# `prop:rounding`, the part independent of the rounding theorem

Integral schedules from a fractional schedule and a sequence of caches, the state right before a time, the lazy caches of a fractional schedule, and facts about finite distributions. Nothing here uses the rounding theorem of Bansal, Buchbinder and Naor; `Rounding/Schedule.lean` builds the random schedule on top of it.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

namespace Rounding

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The indicator vector of a set of pages. -/
def indicator (C : Finset Page) : Page → ℝ := fun i => if i ∈ C then 1 else 0

open scoped InstanceNotation in
/-- Power-of-two weights differ by a factor of at least `2` if they differ. -/
theorem two_mul_le_of_powerOfTwo {input : Instance Page} (h2 : input.PowerOfTwoWeights)
    (i j : Page) (h : w i < w j) : 2 * w i ≤ w j := by
  obtain ⟨a, ha⟩ := h2 i
  obtain ⟨b, hb⟩ := h2 j
  rw [ha, hb] at h ⊢
  have hab : a < b := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h
  calc 2 * (2 : ℝ) ^ a = 2 ^ (a + 1) := by rw [zpow_add_one₀ two_ne_zero, mul_comm]
    _ ≤ 2 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)


/-- The lazy fractional caches `y⁽ᵛ⁾` of the states of `X`. -/
noncomputable def lazyCaches (input : Instance Page) (X : FracSchedule Page) :
    List (Page → ℝ) :=
  lazySeq input.cacheSize (X.map fun w => zmap input.delta w.state)

/-- The integral schedule that moves to the cache `C⁽ᵛ⁾` at the time of the `ν`-th waypoint. -/
def toSchedule (X : FracSchedule Page) (Cs : List (Finset Page)) : Schedule Page :=
  List.zipWith (fun w C => ⟨w.time, C⟩) X Cs



/-! ### Chronological lists -/

section Lists

variable {α : Type*} {R : α → α → Prop} {P : α → Bool}

/-- In a list ordered by `R`, filtering by a predicate inherited by earlier elements keeps a prefix. -/
theorem filter_eq_take (hP : ∀ x y, R x y → P y → P x) {l : List α} (hl : l.Pairwise R) :
    l.filter P = l.take (l.filter P).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : P x
    · rw [List.filter_cons_of_pos hx, List.length_cons, List.take_succ_cons, ← ih hl.2]
    · have : l.filter P = [] :=
        List.filter_eq_nil_iff.2 fun y hy hPy => hx (hP x y (hl.1 y hy) hPy)
      rw [List.filter_cons_of_neg hx, this]
      rfl

/-- The same by index: the predicate holds exactly at the indices below the length of the filtered list. -/
theorem getElem_iff_lt_length_filter (hP : ∀ x y, R x y → P y → P x) {l : List α}
    (hl : l.Pairwise R) (j : ℕ) (hj : j < l.length) : P l[j] ↔ j < (l.filter P).length := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : P x
    · rw [List.filter_cons_of_pos hx, List.length_cons]
      cases j with
      | zero => simp [hx]
      | succ j => simpa using ih hl.2 j (by simpa using hj)
    · have : l.filter P = [] :=
        List.filter_eq_nil_iff.2 fun y hy hPy => hx (hP x y (hl.1 y hy) hPy)
      rw [List.filter_cons_of_neg hx, this]
      cases j with
      | zero => simpa using hx
      | succ j =>
        simp only [List.getElem_cons_succ, List.length_nil, Nat.not_lt_zero, iff_false]
        exact List.filter_eq_nil_iff.1 this _ (List.getElem_mem _)

end Lists

/-! ### The integral schedule of a sequence of caches -/

theorem toSchedule_cons (w : Waypoint Page) (X : FracSchedule Page) (C : Finset Page)
    (Cs : List (Finset Page)) : toSchedule (w :: X) (C :: Cs) = ⟨w.time, C⟩ :: toSchedule X Cs :=
  rfl

theorem length_toSchedule (X : FracSchedule Page) (Cs : List (Finset Page)) :
    (toSchedule X Cs).length = min X.length Cs.length := by
  simp [toSchedule]

theorem getElem_toSchedule {X : FracSchedule Page} {Cs : List (Finset Page)} {j : ℕ}
    (hj : j < (toSchedule X Cs).length) :
    (toSchedule X Cs)[j] = ⟨(X[j]'(by rw [length_toSchedule] at hj; omega)).time,
      Cs[j]'(by rw [length_toSchedule] at hj; omega)⟩ := by
  simp [toSchedule]

/-- The steps of `toSchedule X Cs` are chronological if the waypoints are. -/
theorem toSchedule_chronological {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (Cs : List (Finset Page)) :
    (toSchedule X Cs).Pairwise fun earlier later => earlier.time ≤ later.time := by
  rw [List.pairwise_iff_getElem] at hX ⊢
  intro i j hi hj hij
  rw [getElem_toSchedule, getElem_toSchedule]
  exact hX i j _ _ hij

/-- The steps up to time `t` are those of the waypoints up to time `t`. -/
theorem toSchedule_upTo {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (Cs : List (Finset Page))
    (t : ℝ) :
    Schedule.upTo (toSchedule X Cs) t = toSchedule (X.upTo t) (Cs.take (X.upTo t).length) := by
  induction X generalizing Cs with
  | nil => simp [toSchedule, Schedule.upTo, FracSchedule.upTo]
  | cons w X ih =>
    rw [List.pairwise_cons] at hX
    cases Cs with
    | nil => simp [toSchedule, Schedule.upTo]
    | cons C Cs =>
      have ih' := ih hX.2 Cs
      simp only [Schedule.upTo, FracSchedule.upTo] at ih' ⊢
      rw [toSchedule_cons]
      by_cases hw : w.time ≤ t
      · rw [List.filter_cons_of_pos (by simpa using hw), List.filter_cons_of_pos (by simpa using hw),
          List.length_cons, List.take_succ_cons, toSchedule_cons, ih']
      · have h1 : X.filter (fun w => decide (w.time ≤ t)) = [] :=
          List.filter_eq_nil_iff.2 fun v hv h => hw ((hX.1 v hv).trans (by simpa using h))
        rw [List.filter_cons_of_neg (by simpa using hw), List.filter_cons_of_neg (by simpa using hw),
          ih', h1]
        rfl

/-- The fetch cost of `toSchedule X Cs` starting from `C`. -/
theorem costFrom_toSchedule (w : Page → ℝ) : ∀ (X : FracSchedule Page) (Cs : List (Finset Page))
    (C : Finset Page), Cs.length ≤ X.length →
    Schedule.costFrom w C (toSchedule X Cs) = ∑ i ∈ Cs.getD 0 ∅ \ C, w i +
      ∑ ν ∈ Finset.range (Cs.length - 1), ∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, w i
  | _, [], C, _ => by simp [toSchedule, Schedule.costFrom]
  | [], _ :: _, _, h => by simp at h
  | x :: X, C' :: Cs, C, h => by
      rw [toSchedule_cons, Schedule.costFrom,
        costFrom_toSchedule w X Cs C' (by simpa using h)]
      rcases Cs with _ | ⟨C'', Cs⟩
      · simp
      · simp only [List.length_cons, Nat.add_sub_cancel, Finset.sum_range_succ' _ (Cs.length)]
        simp
        ring

/-- The cache of step `ν` is present at every time `s` from the time of waypoint `ν` to the time of the next waypoint. -/
theorem cachedAt_toSchedule {input : Instance Page} {X : FracSchedule Page}
    {Cs : List (Finset Page)} (hlen : Cs.length = X.length) {ν : ℕ} (hν : ν < X.length) {s : ℝ}
    (h1 : X[ν].time ≤ s) (h2 : ∀ h : ν + 1 < X.length, s ≤ X[ν + 1].time) {p : Page}
    (hp : p ∈ Cs[ν]'(hlen ▸ hν)) : Schedule.CachedAt input (toSchedule X Cs) p s := by
  have hS : ν < (toSchedule X Cs).length := by rw [length_toSchedule]; omega
  refine Or.inr ⟨ν, hS, ?_, ?_, ?_⟩
  · rw [getElem_toSchedule]; exact h1
  · intro step hstep
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hstep
    rw [getElem_toSchedule]
    exact h2 (by rw [length_toSchedule] at h; omega)
  · rw [getElem_toSchedule]; exact hp

/-- The initial cache is present until the time of the first waypoint. -/
theorem cachedAt_toSchedule_initial {input : Instance Page} {X : FracSchedule Page}
    {Cs : List (Finset Page)} (hlen : Cs.length = X.length)
    (h0 : ∀ C ∈ Cs.head?, C = input.initialCache) (hpos : 0 < X.length) {s : ℝ}
    (hs : s ≤ X[0].time) {p : Page} (hp : p ∈ Cs[0]'(hlen ▸ hpos)) :
    Schedule.CachedAt input (toSchedule X Cs) p s := by
  obtain ⟨w, X', rfl⟩ := List.exists_cons_of_length_pos hpos
  obtain ⟨C, Cs', rfl⟩ := List.exists_cons_of_length_pos (hlen ▸ hpos)
  refine Or.inl ⟨?_, ?_⟩
  · rw [← h0 C rfl]; simpa using hp
  · intro step hstep
    simp only [toSchedule_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hstep
    subst hstep
    simpa using hs

/-! ### The state right before a time -/

/-- The index of the waypoint giving the state right before time `t`: the last waypoint with time `< t`, or the first one if there is none. -/
noncomputable def beforeIdx (X : FracSchedule Page) (t : ℝ) : ℕ :=
  (X.filter fun w => decide (w.time < t)).length - 1

theorem beforeIdx_lt {X : FracSchedule Page} (hpos : 0 < X.length) (t : ℝ) :
    beforeIdx X t < X.length := by
  have := List.length_filter_le (fun w : Waypoint Page => decide (w.time < t)) X
  unfold beforeIdx
  omega

/-- Waypoints with time `< t` come first. -/
theorem lt_iff_lt_length_filter {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (t : ℝ) (j : ℕ)
    (hj : j < X.length) : X[j].time < t ↔ j < (X.filter fun w => decide (w.time < t)).length := by
  rw [← getElem_iff_lt_length_filter (P := fun w : Waypoint Page => decide (w.time < t))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hX j hj]
  simp

theorem stateBefore_eq {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (hpos : 0 < X.length)
    (t : ℝ) : X.stateBefore t = (X[beforeIdx X t]'(beforeIdx_lt hpos t)).state := by
  have hfilt := filter_eq_take (P := fun w : Waypoint Page => decide (w.time < t))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hX
  have hn := List.length_filter_le (fun w : Waypoint Page => decide (w.time < t)) X
  have hb : beforeIdx X t = (X.filter fun w => decide (w.time < t)).length - 1 := rfl
  unfold FracSchedule.stateBefore
  conv_lhs => rw [hfilt, List.getLast?_take]
  split_ifs with h0
  · obtain ⟨w, X', rfl⟩ := List.exists_cons_of_length_pos hpos
    simp only [hb, h0]
    simp
  · rw [List.getElem?_eq_getElem (by omega : _ - 1 < X.length)]
    simp only [hb, Option.some_or]

/-- If the page of `ρ` is in the cache right before its arrival, it is cached at its arrival. -/
theorem cachedAt_arrival {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) {Cs : List (Finset Page)}
    (hlen : Cs.length = X.length) (h0 : ∀ C ∈ Cs.head?, C = input.initialCache)
    (hpos : 0 < X.length) {p : Page} {t : ℝ} (hp : p ∈ Cs.getD (beforeIdx X t) ∅) :
    Schedule.CachedAt input (toSchedule X Cs) p t := by
  have hiff := lt_iff_lt_length_filter hX t
  have hb := beforeIdx_lt hpos t
  rw [List.getD_eq_getElem _ _ (by omega)] at hp
  obtain hn | hn := Nat.eq_zero_or_pos (List.length (X.filter fun w : Waypoint Page => decide (w.time < t)))
  · have hb0 : beforeIdx X t = 0 := by simp only [beforeIdx, hn]
    simp only [hb0] at hp
    exact cachedAt_toSchedule_initial hlen h0 hpos (not_lt.1 fun h => by
      have := (hiff 0 hpos).1 h; omega) hp
  · refine cachedAt_toSchedule hlen hb ((hiff _ hb).2 (by unfold beforeIdx; omega)).le
      (fun h => not_lt.1 fun h' => ?_) hp
    have := (hiff _ h).1 h'
    unfold beforeIdx at this
    omega

/-! ### Laws of finite random caches -/

omit [DecidableEq Page] in
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (Q : PMF α) : ∑ a, (Q a).toReal = 1 := by
  have h := PMF.tsum_coe Q
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top Q a), h, ENNReal.toReal_one]

/-- The probability that page `i` is not cached. -/
theorem sum_not_mem_eq (Q : PMF (Finset Page)) (i : Page) :
    ∑ C : Finset Page, (if i ∈ C then 0 else (Q C).toReal) = 1 - BBN.marginal Q i := by
  rw [BBN.marginal, ← sum_toReal_eq_one Q, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs <;> ring

/-- A page with marginal `1` is in every cache of the support. -/
theorem mem_of_marginal_eq_one {Q : PMF (Finset Page)} {i : Page} (h : BBN.marginal Q i = 1)
    {C : Finset Page} (hC : C ∈ Q.support) : i ∈ C := by
  by_contra hi
  have hs := sum_not_mem_eq Q i
  rw [h, sub_self] at hs
  have hle : (if i ∈ C then 0 else (Q C).toReal) ≤
      ∑ C' : Finset Page, (if i ∈ C' then 0 else (Q C').toReal) :=
    Finset.single_le_sum (f := fun C' => if i ∈ C' then 0 else (Q C').toReal)
      (fun C' _ => by (try dsimp only); split_ifs <;> positivity) (Finset.mem_univ C)
  rw [hs, if_neg hi] at hle
  have h0 : (Q C).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h0 | htop
  · exact (PMF.mem_support_iff _ _).1 hC h0
  · exact PMF.apply_ne_top _ _ htop

omit [Fintype Page] [DecidableEq Page] in
/-- Expectation under an image distribution. -/
theorem tsum_map_mul {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ENNReal) :
    ∑' b, μ.map f b * g b = ∑' a, μ a * g (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  simp_rw [ite_mul, zero_mul]
  simp

omit [Fintype Page] [DecidableEq Page] in
/-- The expectation of a nonnegative function of a finite random variable `f`, as a real sum over the law of `f`. -/
theorem tsum_mul_ofReal_eq {α β : Type*} [Fintype β] (μ : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∑' a, μ a * ENNReal.ofReal (g (f a)) = ENNReal.ofReal (∑ b, (μ.map f b).toReal * g b) := by
  rw [← tsum_map_mul μ f (fun b => ENNReal.ofReal (g b)), tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg ENNReal.toReal_nonneg (hg b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

omit [Fintype Page] [DecidableEq Page] in
/-- Linearity of expectation for a list sum. -/
theorem tsum_mul_list_sum {α ι : Type*} (μ : α → ENNReal) (l : List ι) (g : ι → α → ENNReal) :
    ∑' a, μ a * (l.map fun i => g i a).sum = (l.map fun i => ∑' a, μ a * g i a).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

omit [Fintype Page] [DecidableEq Page] in
theorem ofReal_list_sum {ι : Type*} (l : List ι) (f : ι → ℝ) (hf : ∀ i ∈ l, 0 ≤ f i) :
    ENNReal.ofReal (l.map f).sum = (l.map fun i => ENNReal.ofReal (f i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hf a List.mem_cons_self) (List.sum_nonneg fun x hx => ?_),
      ih fun i hi => hf i (List.mem_cons_of_mem _ hi)]
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact hf j (List.mem_cons_of_mem _ hj)


theorem lazyCaches_take (input : Instance Page) (X : FracSchedule Page) (m : ℕ) :
    lazyCaches input (X.take m) = (lazyCaches input X).take m := by
  rw [lazyCaches, lazyCaches, lazySeq_take, List.map_take]

theorem sum_indicator (C : Finset Page) : ∑ i, indicator C i = C.card := by
  simp [indicator]

/-- The cached masses `z⁽ᵛ⁾ = zmap δ x⁽ᵛ⁾` of the states of `X`. -/
theorem zs_spec {input : Instance Page} {X : FracSchedule Page} (hX : X.Feasible input) :
    ∀ z ∈ X.map (fun w => zmap input.delta w.state),
      (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ input.cacheSize := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
  exact zmap_mem_fracCaches_le input.cacheSize_pos rfl (hX.bounds w hw) (hX.mass w hw)

theorem zs_head {input : Instance Page} {X : FracSchedule Page}
    (h0 : ∀ w ∈ X.head?, zmap input.delta w.state = indicator input.initialCache) :
    ∀ z ∈ (X.map fun w => zmap input.delta w.state).head?, ∑ i, z i = input.cacheSize := by
  intro z hz
  simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [h0 w hw, sum_indicator, input.initialCache_card]


omit [DecidableEq Page] in
open scoped InstanceNotation in
/-- The fractional fetch cost by index. -/
theorem fracFetchCost_eq (input : Instance Page) (X : FracSchedule Page) :
    X.fetchCost input = ∑ ν ∈ Finset.range (X.length - 1), ∑ i, w i *
      max 0 ((X.map Waypoint.state).getD ν 0 i - (X.map Waypoint.state).getD (ν + 1) 0 i) := by
  induction X with
  | nil => simp [FracSchedule.fetchCost]
  | cons a X ih =>
    cases X with
    | nil => simp [FracSchedule.fetchCost]
    | cons b rest =>
      rw [FracSchedule.fetchCost, ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ' _ (rest.length)]
      simp
      ring

/-! ### Delay costs -/

/-- The fractional service time is attained at a waypoint. -/
theorem exists_fracServiceTime {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Feasible input) {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ ν, ∃ hν : ν < X.length, ρ.arrival ≤ X[ν].time ∧ X[ν].state ρ.page = input.delta ∧
      X[ν].time = X.serviceTime input ρ := by
  have hne : {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧
      w.time = s}.Nonempty := by
    obtain ⟨w, hw, h1, h2⟩ := hX.serves ρ hρ
    exact ⟨w.time, w, hw, h1, h2, rfl⟩
  have hfin : {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧
      w.time = s}.Finite :=
    (X.map Waypoint.time).finite_toSet.subset fun s ⟨w, hw, _, _, hs⟩ =>
      List.mem_map.2 ⟨w, hw, hs⟩
  obtain ⟨w, hw, h1, h2, h3⟩ := hne.csInf_mem hfin
  obtain ⟨ν, hν, rfl⟩ := List.getElem_of_mem hw
  exact ⟨ν, hν, h1, h2, h3⟩


theorem getD_zs {δ : ℝ} {X : FracSchedule Page} {j : ℕ} (hj : j < X.length) :
    (X.map fun w => zmap δ w.state).getD j 0 = zmap δ ((X.map Waypoint.state).getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
  simp


end Rounding

end PagingWithDelay
end

/-! ## Inlined from `Milestones.Theorem1.Offline` -/
section

/-!
# Theorem 1, offline side: platform instances and schedules as instances and schedules of
`PagingWithDelay`

* `conv`: a platform request as a request of `PagingWithDelay` (delay `x ↦ d(x⁺)`); for an
  invalid request, an arbitrary valid delay function.
* `inst`: the platform data `(n, k, w, O₀, σ)` with `k < n` as an instance of `PagingWithDelay`.
* `firstTime`: the minimum of a list.
* `costWith_le`: every platform-valid schedule `s` of finite platform cost gives a feasible
  schedule of `PagingWithDelay` (same steps) together with service times at which its cost is
  `(totalCost s).toReal`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Thm1

open PagingDelay.PMD

/-! ### Requests -/

/-- The delay function `x ↦ d(x⁺)` of a valid platform request is a valid delay function on `ℝ`. -/
lemma valid_ext {n : ℕ} {r : Request n} (h : ValidRequest r) :
    Monotone (fun x : ℝ => (r.delay x.toNNReal : ℝ)) ∧
      Continuous (fun x : ℝ => (r.delay x.toNNReal : ℝ)) ∧
      (fun x : ℝ => (r.delay x.toNNReal : ℝ)) 0 = 0 ∧
      ∀ M : ℝ, ∃ τ, M ≤ (fun x : ℝ => (r.delay x.toNNReal : ℝ)) τ := by
  obtain ⟨-, hmono, hcont, h0, hunb⟩ := h
  refine ⟨fun a b hab => ?_, ?_, ?_, fun M => ?_⟩
  · exact NNReal.coe_le_coe.2 (hmono (Real.toNNReal_le_toNNReal hab))
  · exact NNReal.continuous_coe.comp (hcont.comp continuous_real_toNNReal)
  · simp [h0]
  · obtain ⟨t, ht⟩ := hunb M.toNNReal
    refine ⟨t, ?_⟩
    simp only [Real.toNNReal_coe]
    have := NNReal.coe_lt_coe.2 ht
    have h2 : M ≤ (M.toNNReal : ℝ) := Real.le_coe_toNNReal M
    linarith

open Classical in
/-- A platform request as a request of `PagingWithDelay`. -/
def conv {n : ℕ} (r : Request n) : PagingWithDelay.Request (Fin n) :=
  if h : ValidRequest r then
    { page := r.page, arrival := r.arrival, delay := fun x => (r.delay x.toNNReal : ℝ),
      delay_mono := (valid_ext h).1, delay_continuous := (valid_ext h).2.1,
      delay_zero := (valid_ext h).2.2.1, delay_unbounded := (valid_ext h).2.2.2 }
  else
    { page := r.page, arrival := r.arrival, delay := fun x => max x 0,
      delay_mono := fun a b hab => max_le_max hab le_rfl,
      delay_continuous := continuous_id.max continuous_const,
      delay_zero := by simp,
      delay_unbounded := fun M => ⟨M, le_max_left _ _⟩ }

@[simp] lemma conv_page {n : ℕ} (r : Request n) : (conv r).page = r.page := by
  unfold conv; split <;> rfl

@[simp] lemma conv_arrival {n : ℕ} (r : Request n) : (conv r).arrival = r.arrival := by
  unfold conv; split <;> rfl

lemma conv_delay {n : ℕ} {r : Request n} (h : ValidRequest r) (x : ℝ) :
    (conv r).delay x = (r.delay x.toNNReal : ℝ) := by
  unfold conv; rw [dif_pos h]

/-! ### Instances -/

lemma exists_not_mem_of_card {n k : ℕ} (hkn : k < n) {C : Finset (Fin n)} (hC : C.card = k) :
    ∃ i, i ∉ C := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := C) (t := Finset.univ) (by simpa [hC] using hkn)
  exact ⟨i, hi⟩

/-- The platform data as an instance of `PagingWithDelay`. -/
def inst (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k) (σ : Instance n) :
    PagingWithDelay.Instance (Fin n) where
  weight := w
  weight_pos := hw
  cacheSize := k
  cacheSize_pos := hk
  cacheSize_lt := by simpa using hkn
  initialCache := O₀
  initialCache_card := hO₀
  startPage := Classical.choose (exists_not_mem_of_card hkn hO₀)
  startPage_not_mem := Classical.choose_spec (exists_not_mem_of_card hkn hO₀)
  tieRank := fun i => i.val
  requests := σ.map conv

lemma inst_upTo {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {σ σ' : Instance n} {t : ℝ}
    (h : revealed σ t = revealed σ' t) :
    (inst n k hk hkn w hw O₀ hO₀ σ).upTo t = (inst n k hk hkn w hw O₀ hO₀ σ').upTo t := by
  have key : ∀ τ : Instance n, ((τ.map conv).filter fun ρ => decide (ρ.arrival ≤ t)) =
      (revealed τ t).map conv := by
    intro τ
    simp only [revealed, List.filter_map, Function.comp_def, conv_arrival]
  simp only [PagingWithDelay.Instance.upTo, inst, key, h]

/-! ### First times -/

lemma firstTime_cons (t : ℝ) (ts : List ℝ) :
    firstTime (t :: ts) = some (match firstTime ts with | none => t | some u => min t u) := rfl

lemma firstTime_spec : ∀ {ts : List ℝ} {t : ℝ}, firstTime ts = some t →
    t ∈ ts ∧ ∀ u ∈ ts, t ≤ u
  | [], t, h => by simp [firstTime] at h
  | a :: ts, t, h => by
    rw [firstTime_cons] at h
    cases h' : firstTime ts with
    | none =>
      rw [h'] at h
      simp only [Option.some.injEq] at h
      subst h
      have : ts = [] := by
        cases ts with
        | nil => rfl
        | cons b ts => rw [firstTime_cons] at h'; simp at h'
      subst this
      simp
    | some u =>
      rw [h'] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hu, hmin⟩ := firstTime_spec h'
      refine ⟨?_, ?_⟩
      · rcases min_choice a u with e | e <;> rw [e]
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hu
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hmin v hv)

lemma firstTime_of_mem : ∀ {ts : List ℝ} {t : ℝ}, t ∈ ts → ∃ u, firstTime ts = some u
  | [], t, h => by simp at h
  | a :: ts, t, h => ⟨_, firstTime_cons a ts⟩

/-! ### Measurability of functions of finitely many random sets -/

/-- A function of a random variable with finitely many values, each of measurable preimage, is
measurable. -/
lemma measurable_comp_of_finite {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    [Finite β] (g : Ω → β) (hg : ∀ b, MeasurableSet (g ⁻¹' {b})) (f : β → γ) :
    Measurable (f ∘ g) := by
  intro S _
  have : f ∘ g ⁻¹' S = ⋃ b ∈ f ⁻¹' S, g ⁻¹' {b} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun b _ => hg b

/-- A vector of random sets, each membership event measurable: each value has a measurable
preimage. -/
lemma measurableSet_preimage_vec {Ω : Type*} [MeasurableSpace Ω] {N n : ℕ}
    (V : Ω → Fin N → Finset (Fin n)) (hV : ∀ j i, MeasurableSet {ω | i ∈ V ω j})
    (v : Fin N → Finset (Fin n)) : MeasurableSet (V ⁻¹' {v}) := by
  have : V ⁻¹' {v} = ⋂ j, ⋂ i, {ω | i ∈ V ω j ↔ i ∈ v j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro rfl j i; rfl
    · intro h; funext j; ext i; exact h j i
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ v j
  · have : {ω | i ∈ V ω j ↔ i ∈ v j} = {ω | i ∈ V ω j} := by ext; simp [hi]
    rw [this]; exact hV j i
  · have : {ω | i ∈ V ω j ↔ i ∈ v j} = {ω | i ∈ V ω j}ᶜ := by ext; simp [hi]
    rw [this]; exact (hV j i).compl

/-! ### Offline schedules -/

/-- A platform schedule as a schedule of `PagingWithDelay`. -/
def toSteps {n : ℕ} (s : Schedule n) : PagingWithDelay.Schedule (Fin n) :=
  s.map fun e => ⟨e.time, e.cache⟩

lemma fetchCostFrom_eq {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ (c : Finset (Fin n)) (s : Schedule n),
      fetchCostFrom w c s = ENNReal.ofReal (PagingWithDelay.Schedule.costFrom w c (toSteps s))
  | c, [] => by simp [fetchCostFrom, toSteps, PagingWithDelay.Schedule.costFrom]
  | c, e :: es => by
    rw [fetchCostFrom, fetchCostFrom_eq w hw e.cache es]
    simp only [toSteps, List.map_cons, PagingWithDelay.Schedule.costFrom]
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => (hw i).le)
      (PagingWithDelay.PMD.MainProof.costFrom_nonneg w (fun i => (hw i).le) _ _),
      ENNReal.ofReal_sum_of_nonneg fun i _ => (hw i).le]

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k)

local notation "J" => inst n k hk hkn w hw O₀ hO₀

/-- In a chronological schedule, the cache right before `a` is cached at `a`. -/
lemma cachedAt_of_cacheBefore {σ : Instance n} {s : Schedule n}
    (hs : s.Pairwise fun e f => e.time ≤ f.time) {p : Fin n} {a : ℝ}
    (hp : p ∈ cacheBefore O₀ s a) :
    PagingWithDelay.Schedule.CachedAt (J σ) (toSteps s) p a := by
  have hfilt := PagingWithDelay.Rounding.filter_eq_take
    (P := fun e : CacheEvent n => decide (e.time < a))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hs
  have hiff := PagingWithDelay.Rounding.getElem_iff_lt_length_filter
    (P := fun e : CacheEvent n => decide (e.time < a))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hs
  set m := (s.filter fun e => decide (e.time < a)).length with hm
  unfold cacheBefore at hp
  rw [hfilt] at hp
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0] at hp
    simp only [List.take_zero, List.map_nil, List.getLastD_nil] at hp
    refine Or.inl ⟨hp, fun step hstep => ?_⟩
    cases s with
    | nil => simp [toSteps] at hstep
    | cons e es =>
      simp only [toSteps, List.map_cons, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hstep
      subst hstep
      have := (hiff 0 (by simp)).not.2 (by omega)
      simpa using this
  · have hms : m ≤ s.length := List.length_filter_le _ _
    have hj : m - 1 < s.length := by omega
    have hlast : ((s.take m).map CacheEvent.cache).getLastD O₀ = s[m - 1].cache := by
      rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_take]
      simp [show m ≠ 0 by omega, List.getElem?_eq_getElem hj]
    rw [hlast] at hp
    refine Or.inr ⟨m - 1, by simpa [toSteps] using hj, ?_, ?_, ?_⟩
    · simp only [toSteps, List.getElem_map]
      have := (hiff (m - 1) hj).2 (by omega)
      simp only [decide_eq_true_eq] at this
      exact this.le
    · intro step hstep
      simp only [toSteps, List.getElem?_map, Option.mem_def, Option.map_eq_some_iff] at hstep
      obtain ⟨e, he, rfl⟩ := hstep
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 he
      have := (hiff (m - 1 + 1) hlt).not.2 (by omega)
      simpa using this
    · simpa [toSteps] using hp

/-- In a chronological schedule, the cache of a step is cached at the time of the step. -/
lemma cachedAt_of_mem {σ : Instance n} {s : Schedule n}
    (hs : s.Pairwise fun e f => e.time ≤ f.time) {e : CacheEvent n} (he : e ∈ s) {p : Fin n}
    (hp : p ∈ e.cache) :
    PagingWithDelay.Schedule.CachedAt (J σ) (toSteps s) p e.time := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  refine Or.inr ⟨j, by simpa [toSteps] using hj, by simp [toSteps], ?_, by simpa [toSteps] using hp⟩
  intro step hstep
  simp only [toSteps, List.getElem?_map, Option.mem_def, Option.map_eq_some_iff] at hstep
  obtain ⟨f, hf, rfl⟩ := hstep
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hf
  exact List.pairwise_iff_getElem.1 hs j (j + 1) hj hlt (by omega)

/-- A served request is served at a time at which its page is cached. -/
lemma serviceTime_spec {σ : Instance n} {s : Schedule n}
    (hs : s.Pairwise fun e f => e.time ≤ f.time) {r : Request n} {t : ℝ}
    (ht : serviceTime O₀ s r = some t) :
    r.arrival ≤ t ∧ PagingWithDelay.Schedule.CachedAt (J σ) (toSteps s) r.page t := by
  obtain ⟨hmem, -⟩ := firstTime_spec ht
  rcases List.mem_append.1 hmem with h | h
  · split_ifs at h with hp
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨le_rfl, cachedAt_of_cacheBefore hk hkn hw hO₀ hs hp⟩
    · simp at h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    obtain ⟨he, h1, h2⟩ : e ∈ s ∧ r.arrival ≤ e.time ∧ r.page ∈ e.cache := by
      simpa using he
    exact ⟨h1, cachedAt_of_mem hk hkn hw hO₀ hs he h2⟩

/-- Every platform-valid schedule of finite cost on a valid instance gives a feasible schedule
of `PagingWithDelay` with service times at which its cost is the platform cost. -/
theorem exists_costWith {σ : Instance n} (hσ : ValidInstance σ) {s : Schedule n}
    (hs : ScheduleValid k O₀ s) (hfin : totalCost w O₀ s σ ≠ ⊤) :
    ∃ τ : PagingWithDelay.Request (Fin n) → ℝ,
      (toSteps s).Feasible (J σ) ∧ (toSteps s).ServiceTimes (J σ) τ ∧
      ENNReal.ofReal ((toSteps s).costWith (J σ) τ) = totalCost w O₀ s σ := by
  classical
  have hchron := hs.2.2
  -- every request is served
  have hserved : ∀ r ∈ σ, ∃ t, serviceTime O₀ s r = some t := by
    intro r hr
    by_contra hnone
    push Not at hnone
    have hnone' : serviceTime O₀ s r = none := by
      cases h : serviceTime O₀ s r with
      | none => rfl
      | some t => exact absurd h (hnone t)
    apply hfin
    unfold totalCost delayCost
    have hle : requestDelay r (serviceTime O₀ s r) ≤
        (σ.map fun r => requestDelay r (serviceTime O₀ s r)).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨r, hr, rfl⟩)
    rw [hnone'] at hle
    exact top_le_iff.1 ((le_of_eq rfl).trans (hle.trans le_add_self))
  -- the service time of a request of `J σ`
  let tOf : Request n → ℝ := fun r => (serviceTime O₀ s r).getD 0
  have htOf : ∀ r ∈ σ, serviceTime O₀ s r = some (tOf r) := by
    intro r hr
    obtain ⟨t, ht⟩ := hserved r hr
    simp [tOf, ht]
  -- a request of `J σ` comes from a request of `σ`
  have hpre : ∀ ρ ∈ (J σ).requests, ∃ r ∈ σ, conv r = ρ := fun ρ hρ => List.mem_map.1 hρ
  let τ : PagingWithDelay.Request (Fin n) → ℝ := fun ρ =>
    if h : ∃ r ∈ σ, conv r = ρ then tOf h.choose else 0
  have hτ : ∀ r ∈ σ, τ (conv r) = tOf r := by
    intro r hr
    have h : ∃ r' ∈ σ, conv r' = conv r := ⟨r, hr, rfl⟩
    simp only [τ, dif_pos h]
    obtain ⟨hr', hcr⟩ := h.choose_spec
    -- two requests with the same conversion have the same page and arrival, hence the same
    -- service time
    have hpage : h.choose.page = r.page := by
      have := congrArg PagingWithDelay.Request.page hcr; simpa using this
    have harr : h.choose.arrival = r.arrival := by
      have := congrArg PagingWithDelay.Request.arrival hcr; simpa using this
    simp only [tOf, serviceTime, hpage, harr]
  have hST : (toSteps s).ServiceTimes (J σ) τ := by
    intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := hpre ρ hρ
    rw [hτ r hr, conv_arrival, conv_page]
    exact serviceTime_spec hk hkn hw hO₀ hchron (htOf r hr)
  have hF : (toSteps s).Feasible (J σ) := by
    refine ⟨?_, ?_, fun ρ hρ => ⟨τ ρ, hST ρ hρ⟩⟩
    · simpa [toSteps, List.pairwise_map] using hchron
    · intro step hstep
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hstep
      exact (hs.2.1 e he).2
  refine ⟨τ, hF, hST, ?_⟩
  -- the costs agree
  rw [PagingWithDelay.Schedule.costWith, PagingWithDelay.Schedule.fetchCost, totalCost,
    fetchCostFrom_eq w hw]
  have hd : ∀ r ∈ σ, 0 ≤ (conv r).delay (τ (conv r) - (conv r).arrival) := by
    intro r hr
    rw [conv_delay (hσ r hr)]
    exact NNReal.coe_nonneg _
  have hsum : ((J σ).requests.map fun ρ => ρ.delay (τ ρ - ρ.arrival)).sum =
      (σ.map fun r => (conv r).delay (τ (conv r) - (conv r).arrival)).sum := by
    simp [inst, List.map_map, Function.comp_def]
  change ENNReal.ofReal (PagingWithDelay.Schedule.costFrom w O₀ (toSteps s) + _) = _
  rw [hsum, ENNReal.ofReal_add (PagingWithDelay.PMD.MainProof.costFrom_nonneg w
    (fun i => (hw i).le) _ _) (List.sum_nonneg fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx; exact hd r hr)]
  congr 1
  rw [PagingWithDelay.Rounding.ofReal_list_sum _ _ hd, delayCost]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [htOf r hr, requestDelay, hτ r hr, conv_delay (hσ r hr), conv_arrival,
    ENNReal.ofReal_coe_nnreal]

end

end PagingDelay.PMD.Thm1
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

lemma exists_not_mem_of_card {n k : ℕ} (hkn : k < n) {C : Finset (Fin n)} (hC : C.card = k) :
    ∃ i, i ∉ C := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := C) (t := Finset.univ) (by simpa [hC] using hkn)
  exact ⟨i, hi⟩

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
  startPage := Classical.choose
    (exists_not_mem_of_card hkn (Classical.choose_spec (exists_initialCache n k hkn)))
  startPage_not_mem := Classical.choose_spec
    (exists_not_mem_of_card hkn (Classical.choose_spec (exists_initialCache n k hkn)))
  tieRank := fun i => i.val
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

/-! ## Inlined from `Milestones.Sim.Defs` -/
section

/-!
# Simulation bridge: shared definitions

The dictionary of `Milestones/Sim/Spec.lean` (`simInst`, `view`, `entryMoves`, `logMoves`, `J`),
verbatim, so that the bridge proof (`Milestones/Sim/Bridge.lean`) and the interface can share it.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD

/-- The platform data, with initial page `i₀` and tie order `π`, as an instance of
`PagingWithDelay`. -/
def simInst (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k) (i₀ : Fin n) (hi₀ : i₀ ∉ O₀)
    (π : Fin n ≃ Fin n) (σ : Instance n) : PagingWithDelay.Instance (Fin n) :=
  { Thm1.inst n k hk hkn w hw O₀ hO₀ σ with
    startPage := i₀
    startPage_not_mem := hi₀
    tieRank := fun i => (π i).val }

/-- What the milestones see of a platform move. -/
def view {n : ℕ} (m : Move n) : MoveKind n × (Fin n → ℝ) × (Fin n → ℝ) × ℝ :=
  (m.kind, m.before.x, m.after.x, m.after.time)

/-- The platform moves (as views) recorded by the entry `(s, m)` of our log. -/
def entryMoves {n : ℕ} (J : PagingWithDelay.Instance (Fin n))
    (s : PagingWithDelay.PMD.Snap (Fin n)) :
    PagingWithDelay.PMD.Move (Fin n) → List (MoveKind n × (Fin n → ℝ) × (Fin n → ℝ) × ℝ)
  | .critical p => [(.critical p, s.x, PagingWithDelay.PMD.criticalState J s.x p, s.now)]
  | .openHole e => [(.openHole e.toNat, s.x, PagingWithDelay.PMD.hole J s.x e, s.now)]
  | .trip _ ρ =>
      [(.visit ρ.page, s.x, Function.update s.x ρ.page J.delta, s.now),
       (.returnTrip ρ.page, Function.update s.x ρ.page J.delta, s.x, s.now)]
  | .closeHole e _ =>
      match s.stage with
      | .preempt _ base => [(.closeHole e.toNat, s.x, base, s.now)]
      | _ => []
  | _ => []

/-- All platform moves (as views) recorded by our log. -/
def logMoves {n : ℕ} (J : PagingWithDelay.Instance (Fin n)) :
    List (MoveKind n × (Fin n → ℝ) × (Fin n → ℝ) × ℝ) :=
  (PagingWithDelay.PMD.log J).flatMap fun en => entryMoves J en.1 en.2

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

/-- The instance of the simulation. -/
abbrev J (σ : Instance n) : PagingWithDelay.Instance (Fin n) :=
  simInst n k hk hkn w (Bridge.weight_pos_of_PMDWeights hw) O₀ hO₀ i₀ hi₀ π σ

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Platform` -/
section

/-!
# Simulation bridge: platform-side structure

Facts about the platform's `run` (`Def_PagingDelay_PMD_Algorithm`) that do not mention our event
loop:

* `Chain`: the moves of an execution are chained (`run_chain`); preserved by every operation.
* `runFuel_initial`: the initial snapshot never changes.
* Unfolding lemmas for `preemptiveService` and `roundTrips`, with named pieces `openSnap`,
  `tripList`, `visitSnap`, `tripStep` (verbatim copies of the `let`s of the definitions).
* `pending` under `push` and in time; `fractionalService` of a request arriving after all moves.
* `nextEvent` from the per-page times `nextPageTime`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open scoped BigOperators Classical

variable {n : ℕ}

/-! ### Chains -/

/-- The moves of `e` are chained: each starts where the previous one ended (the first at
`e.initial`), and `e.current` is the end of the last one. -/
def Chain (e : Execution n) : Prop :=
  e.moves.map (fun m => m.before) = (e.initial :: e.moves.map (fun m => m.after)).dropLast ∧
    e.current = (e.moves.map (fun m => m.after)).getLastD e.initial

lemma chain_start (k : ℕ) (O₀ : Finset (Fin n)) (i₀ : Fin n) : Chain (start k O₀ i₀) := by
  simp [Chain, start]

lemma push_initial (e : Execution n) (s : Snapshot n) (kind : MoveKind n) :
    (push e s kind).initial = e.initial := rfl

lemma push_current (e : Execution n) (s : Snapshot n) (kind : MoveKind n) :
    (push e s kind).current = s := rfl

lemma push_moves (e : Execution n) (s : Snapshot n) (kind : MoveKind n) :
    (push e s kind).moves = e.moves ++ [⟨e.current, s, kind⟩] := rfl

lemma dropLast_append_getLastD {α : Type*} : ∀ (a : α) (L : List α),
    (a :: L).dropLast ++ [L.getLastD a] = a :: L
  | a, [] => rfl
  | a, b :: L => by
    have := dropLast_append_getLastD b L
    simp only [List.dropLast_cons_cons, List.cons_append, List.getLastD_cons] at this ⊢
    rw [this]

lemma chain_push {e : Execution n} (h : Chain e) (s : Snapshot n) (kind : MoveKind n) :
    Chain (push e s kind) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [push_moves, push_initial, List.map_append, List.map_cons, List.map_nil]
    rw [h1, h2, ← List.cons_append, List.dropLast_concat]
    exact dropLast_append_getLastD _ _
  · simp [push_moves, push_current]

lemma chain_roundTrips (k : ℕ) (w : Fin n → ℝ) (j : ℕ) :
    ∀ (E : List (Fin n)) (e : Execution n), Chain e → Chain (roundTrips k w j E e)
  | [], e, h => h
  | q :: qs, e, h => by
    unfold roundTrips
    split_ifs
    · exact chain_roundTrips k w j qs _ (chain_push (chain_push h _ _) _ _)
    · exact h

lemma roundTrips_initial (k : ℕ) (w : Fin n → ℝ) (j : ℕ) :
    ∀ (E : List (Fin n)) (e : Execution n), (roundTrips k w j E e).initial = e.initial
  | [], e => rfl
  | q :: qs, e => by
    unfold roundTrips
    split_ifs
    · exact roundTrips_initial k w j qs _
    · rfl

/-! ### Unfolding the preemptive service and the round trips -/

/-- The cached mass `∑_{i : w_i ≤ 2^j} (1 - x_i)` of the pages of weight `≤ 2^j`. -/
def mass (w : Fin n → ℝ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => w i ≤ level j), (1 - x i)

/-- The condition of the platform's level-`j` preemptive service. -/
def precond (k : ℕ) (w : Fin n → ℝ) (j : ℕ) (e : Execution n) : Prop :=
  e.current.budget j ≥ 4 * level j ∧ mass w j e.current.x ≥ 1 - delta k

/-- The snapshot after opening the level-`j` hole (the `s` of `preemptiveService`). -/
def openSnap (k : ℕ) (w : Fin n → ℝ) (j : ℕ) (e : Execution n) : Snapshot n :=
  let W := level j
  let xstart := e.current.x
  let mass := ∑ i ∈ Finset.univ.filter (fun i => w i ≤ W), (1 - xstart i)
  let θ := if mass = 0 then 0 else (1 - delta k) / mass
  { e.current with
    x := fun i => if w i ≤ W then xstart i + θ * (1 - xstart i) else xstart i
    budget := Function.update e.current.budget j (e.current.budget j - W * (1 - delta k)) }

/-- The platform's list of round-trip pages of level `j` (the `E` of `preemptiveService`). -/
def tripList (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n) (j : ℕ)
    (e : Execution n) : List (Fin n) :=
  let W := level j
  let rs := pending k e σ e.current.time
  (Finset.univ.toList.filter (fun q => w q ≤ W ∧ ∃ r ∈ rs, r.page = q)).mergeSort
    (fun p q => decide (
      let a := effectiveDeadline w rs p e.current.time
      let b := effectiveDeadline w rs q e.current.time
      deadlineLE a b ∧ (a ≠ b ∨ π p ≤ π q)))

lemma preemptiveService_of_not {k : ℕ} {w : Fin n → ℝ} {π : Fin n ≃ Fin n} {σ : Instance n}
    {j : ℕ} {e : Execution n} (h : ¬ precond k w j e) :
    preemptiveService k w π σ j e = e := by
  unfold preemptiveService
  exact if_neg h

lemma preemptiveService_of {k : ℕ} {w : Fin n → ℝ} {π : Fin n ≃ Fin n} {σ : Instance n}
    {j : ℕ} {e : Execution n} (h : precond k w j e) :
    preemptiveService k w π σ j e =
      push (roundTrips k w j (tripList k w π σ j e) (push e (openSnap k w j e) (.openHole j)))
        { (roundTrips k w j (tripList k w π σ j e)
            (push e (openSnap k w j e) (.openHole j))).current with x := e.current.x }
        (.closeHole j) := by
  unfold preemptiveService
  exact if_pos h

lemma chain_preemptiveService (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n)
    (j : ℕ) {e : Execution n} (h : Chain e) : Chain (preemptiveService k w π σ j e) := by
  by_cases hc : precond k w j e
  · rw [preemptiveService_of hc]
    exact chain_push (chain_roundTrips k w j _ _ (chain_push h _ _)) _ _
  · rw [preemptiveService_of_not hc]; exact h

lemma preemptiveService_initial (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n)
    (j : ℕ) (e : Execution n) : (preemptiveService k w π σ j e).initial = e.initial := by
  by_cases hc : precond k w j e
  · rw [preemptiveService_of hc]
    exact roundTrips_initial k w j _ _
  · rw [preemptiveService_of_not hc]

lemma chain_block (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n)
    (js : List ℕ) : ∀ {e : Execution n}, Chain e →
      Chain (js.foldl (fun a j => preemptiveService k w π σ j a) e) := by
  induction js with
  | nil => intro e h; exact h
  | cons j js ih => intro e h; exact ih (chain_preemptiveService k w π σ j h)

lemma block_initial (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n)
    (js : List ℕ) : ∀ (e : Execution n),
      (js.foldl (fun a j => preemptiveService k w π σ j a) e).initial = e.initial := by
  induction js with
  | nil => intro e; rfl
  | cons j js ih => intro e; exact (ih _).trans (preemptiveService_initial k w π σ j e)

lemma chain_runFuel (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n) :
    ∀ (f : ℕ) (e : Execution n), Chain e → Chain (runFuel k w π σ f e)
  | 0, e, h => h
  | f + 1, e, h => by
    unfold runFuel
    split
    · exact h
    · exact chain_runFuel k w π σ f _ (chain_block k w π σ _ (chain_push h _ _))

lemma runFuel_initial (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n) :
    ∀ (f : ℕ) (e : Execution n), (runFuel k w π σ f e).initial = e.initial
  | 0, e => rfl
  | f + 1, e => by
    unfold runFuel
    split
    · rfl
    · exact (runFuel_initial k w π σ f _).trans (block_initial k w π σ _ _)

/-- The snapshot at the bottom of a round trip on `q` (the `s` of `roundTrips`). -/
def visitSnap (k : ℕ) (w : Fin n → ℝ) (j : ℕ) (q : Fin n) (e : Execution n) : Snapshot n :=
  let saved := e.current.x
  { e.current with
    x := Function.update saved q (delta k)
    claims := Function.update e.current.claims q 0
    budget := Function.update e.current.budget j
      (e.current.budget j - w q * (saved q - delta k)) }

/-- A round trip on `q`: the visit and the return. -/
def tripStep (k : ℕ) (w : Fin n → ℝ) (j : ℕ) (q : Fin n) (e : Execution n) : Execution n :=
  push (push e (visitSnap k w j q e) (.visit q))
    { visitSnap k w j q e with x := e.current.x } (.returnTrip q)

lemma roundTrips_nil (k : ℕ) (w : Fin n → ℝ) (j : ℕ) (e : Execution n) :
    roundTrips k w j [] e = e := rfl

lemma roundTrips_cons_of {k : ℕ} {w : Fin n → ℝ} {j : ℕ} {q : Fin n} {qs : List (Fin n)}
    {e : Execution n} (h : e.current.budget j ≥ level j) :
    roundTrips k w j (q :: qs) e = roundTrips k w j qs (tripStep k w j q e) := by
  rw [roundTrips, if_pos h]
  rfl

lemma roundTrips_cons_of_not {k : ℕ} {w : Fin n → ℝ} {j : ℕ} {q : Fin n} {qs : List (Fin n)}
    {e : Execution n} (h : ¬ e.current.budget j ≥ level j) :
    roundTrips k w j (q :: qs) e = e := by
  rw [roundTrips, if_neg h]

/-! ### Pending requests of the platform -/

lemma firstTime_eq_none_iff_nil {ts : List ℝ} : firstTime ts = none ↔ ts = [] := by
  cases ts <;> simp [firstTime]

/-- **Pending after a push.** Pushing a snapshot at a time `≥ t` serves exactly the pending
requests (arrived by `t`) whose page it holds at `δ`.

Proof sketch: `fractionalBefore (push e s kind) r.arrival = fractionalBefore e r.arrival`, since the
new move has time `s.time ≥ t ≥ r.arrival` (not `<`); the second list of `fractionalService` gains
`s.time` iff `s.x r.page = δ` (as `r.arrival ≤ s.time`). `firstTime l = none ↔ l = []`. -/
lemma pending_push (k : ℕ) (σ : Instance n) {e : Execution n} {s : Snapshot n}
    {kind : MoveKind n} {t : ℝ} (ht : t ≤ s.time) :
    pending k (push e s kind) σ t =
      (pending k e σ t).filter (fun r => decide (s.x r.page ≠ delta k)) := by
  unfold pending
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  by_cases ha : r.arrival ≤ t
  · have hle : r.arrival ≤ s.time := ha.trans ht
    have hlt : ¬ s.time < r.arrival := not_lt.mpr hle
    have hfb : fractionalBefore (push e s kind) r.arrival = fractionalBefore e r.arrival := by
      simp [fractionalBefore, push, List.filter_append, hlt]
    simp only [fractionalService, hfb]
    by_cases hx : s.x r.page = delta k <;>
      simp [firstTime_eq_none_iff_nil, push_moves, List.filter_append, ha, hle, hx]
  · simp [ha]

/-- Without arrivals in `(t₁, t₂]`, the pending requests at `t₁` and `t₂` agree (the trace is
fixed; only the arrival filter depends on the time). -/
lemma pending_eq_of_no_arrival (k : ℕ) (σ : Instance n) (e : Execution n) {t₁ t₂ : ℝ}
    (h : ∀ r ∈ σ, ¬ (t₁ < r.arrival ∧ r.arrival ≤ t₂)) (h12 : t₁ ≤ t₂) :
    pending k e σ t₂ = pending k e σ t₁ := by
  unfold pending
  apply List.filter_congr
  intro r hr
  have := h r hr
  by_cases h1 : r.arrival ≤ t₁
  · simp [h1, h1.trans h12]
  · have h2 : ¬ r.arrival ≤ t₂ := fun h2 => this ⟨lt_of_not_ge h1, h2⟩
    simp [h1, h2]

/-- **Service of a fresh request.** If every move of the chained execution `e` ends strictly
before the arrival of `r`, then `r` is served on arrival iff its page is at `δ` in the current
state, and is unserved otherwise.

Proof sketch: `fractionalBefore e r.arrival` takes the last `after.x` of all moves (or
`e.initial.x`), which is `e.current.x` by `Chain`; no move has `r.arrival ≤ after.time`. -/
lemma fractionalService_fresh (k : ℕ) {e : Execution n} (hc : Chain e) {r : Request n}
    (hr : ∀ m ∈ e.moves, m.after.time < r.arrival) :
    fractionalService k e r =
      if e.current.x r.page = delta k then some r.arrival else none := by
  have hb : fractionalBefore e r.arrival = e.current.x := by
    unfold fractionalBefore
    rw [List.filter_eq_self.mpr (fun m hm => by simpa using hr m hm), hc.2,
      ← List.getLastD_map (f := Snapshot.x), List.map_map]
    rfl
  have h3 : e.moves.filter (fun m => decide (r.arrival ≤ m.after.time ∧
      m.after.x r.page = delta k)) = [] :=
    List.filter_eq_nil_iff.mpr (fun m hm => by simp [not_le.mpr (hr m hm)])
  unfold fractionalService
  rw [hb, h3]
  split_ifs <;> simp [firstTime]

/-! ### The next event -/

lemma nextEvent_eq_none_of {k : ℕ} {w : Fin n → ℝ} {π : Fin n ≃ Fin n} {e : Execution n}
    {σ : Instance n} (h : ∀ q, nextPageTime k w e σ q = none) :
    nextEvent k w π e σ = none := by
  unfold nextEvent
  have : (Finset.univ.toList.filterMap
      (fun p => (nextPageTime k w e σ p).map (fun t => (t, p)))) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro p _
    simp [h p]
  rw [this, List.mergeSort_nil]
  rfl

/-- **The next event is the lexicographic minimum** of `(nextPageTime q, π q)`.

Proof sketch: the comparator of `nextEvent` is total and transitive, so `List.sorted_mergeSort`
gives a list sorted by it; its head `h` is `≤` the entry `(t₀, p)`, and `(t₀, p) ≤ h` by `hmin`;
since `π` is injective, `h = (t₀, p)`. -/
lemma nextEvent_eq_some_of_min {k : ℕ} {w : Fin n → ℝ} {π : Fin n ≃ Fin n} {e : Execution n}
    {σ : Instance n} {t₀ : ℝ} {p : Fin n} (hp : nextPageTime k w e σ p = some t₀)
    (hmin : ∀ q t, nextPageTime k w e σ q = some t → t₀ < t ∨ (t₀ = t ∧ π p ≤ π q)) :
    nextEvent k w π e σ = some (t₀, p) := by
  unfold nextEvent
  have hmemL : ∀ a, a ∈ (Finset.univ.toList.filterMap
      (fun p => (nextPageTime k w e σ p).map (fun t => (t, p)))) ↔
        nextPageTime k w e σ a.2 = some a.1 := by
    rintro ⟨t, q⟩
    simp [List.mem_filterMap, Option.map_eq_some_iff]
  generalize Finset.univ.toList.filterMap
    (fun p => (nextPageTime k w e σ p).map (fun t => (t, p))) = L at hmemL ⊢
  have hP := List.pairwise_mergeSort (l := L)
    (le := fun a b : ℝ × Fin n => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ π a.2 ≤ π b.2)))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
      · exact Or.inl (h1.trans h3)
      · exact Or.inl (lt_of_lt_of_eq h1 h3)
      · exact Or.inl (lt_of_eq_of_lt h1 h3)
      · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases lt_trichotomy a.1 b.1 with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases le_total (π a.2) (π b.2) with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
      · exact Or.inr (Or.inl h))
  have hmem : (t₀, p) ∈ L.mergeSort (fun a b : ℝ × Fin n =>
      decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ π a.2 ≤ π b.2))) :=
    List.mem_mergeSort.mpr ((hmemL (t₀, p)).mpr hp)
  have hsub : ∀ a ∈ L.mergeSort (fun a b : ℝ × Fin n =>
      decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ π a.2 ≤ π b.2))), nextPageTime k w e σ a.2 = some a.1 :=
    fun a ha => (hmemL a).mp (List.mem_mergeSort.mp ha)
  revert hP hmem hsub
  generalize L.mergeSort _ = M
  intro hP hmem hsub
  rcases M with _ | ⟨⟨t, q⟩, tl⟩
  · simp at hmem
  · rcases List.mem_cons.mp hmem with heq | htl
    · rw [heq]; rfl
    · have hle := List.rel_of_pairwise_cons hP htl
      simp only [decide_eq_true_eq] at hle
      rcases hmin q t (hsub (t, q) List.mem_cons_self) with h1 | ⟨h1, h2⟩
      · exfalso
        rcases hle with h3 | ⟨h3, -⟩ <;> linarith
      · rcases hle with h3 | ⟨-, h4⟩
        · linarith
        · have : q = p := π.injective (le_antisymm h4 h2)
          rw [h1, this]; rfl

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Dict` -/
section

/-!
# Simulation bridge: dictionary for the instance `J`

The platform's notions in terms of ours, on the instance `J = simInst …` of the simulation:
parameters, paths, levels and deposits, holes, delays, overshoots, the trigger, deadlines.

Throughout, `P` is one of our pending lists and `rs` a list of platform requests with
`(rs.map conv).Perm P` (in the simulation, `rs` is the platform's `pending k e σ t`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open scoped BigOperators
open PagingWithDelay.PMD (serviceEnd criticalState minLevel maxLevel levelWeight levelLen hole
  TriggerCond pageDeadline deposit)

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

/-! ### Parameters -/

lemma J_weight : (I).weight = w := rfl
lemma J_cacheSize : (I).cacheSize = k := rfl
lemma J_delta : (I).delta = delta k := rfl
lemma J_L : (I).L = logFactor k := rfl
lemma J_requests : (I).requests = σ.map Thm1.conv := rfl
lemma J_tieRank (i : Fin n) : (I).tieRank i = (π i).val := rfl
lemma J_initialCache : (I).initialCache = O₀ := rfl
lemma J_startPage : (I).startPage = i₀ := rfl

/-! ### States and paths -/

lemma isRest_iff' (x : Fin n → ℝ) : PagingWithDelay.PMD.IsRest I x ↔ StateValid k x := by
  simp [PagingWithDelay.PMD.IsRest, PagingWithDelay.PMD.IsFrac, StateValid,
    PagingWithDelay.PMD.restMass, simInst, Thm1.inst, PagingWithDelay.Instance.delta, delta]

lemma serviceEnd_eq_bridge (x : Fin n → ℝ) (p : Fin n) :
    serviceEnd I x p =
      serviceEnd (Bridge.inst n k hk hkn w (Bridge.weight_pos_of_PMDWeights hw)) x p := rfl

lemma pathLength_eq' {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n) :
    pathLength k w x p = serviceEnd I x p := by
  rw [serviceEnd_eq_bridge]
  exact Bridge.pathLength_eq hk hkn _ hx p

lemma pathEnd_eq' {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n) :
    pathEnd k w x p = criticalState I x p := by
  rw [Bridge.pathEnd_eq hk hkn (Bridge.weight_pos_of_PMDWeights hw) hx p]
  rfl

/-! ### Levels -/

lemma levelWeight_natCast (j : ℕ) : levelWeight (j : ℤ) = level j := by
  simp [levelWeight, level]

lemma pageLevel_le_iff (q : Fin n) (j : ℕ) :
    PagingWithDelay.PMD.level I q ≤ j ↔ w q ≤ level j := by
  rw [PagingWithDelay.PMD.level_le_iff (I).valid, levelWeight_natCast]
  rfl

/-- Under `PMDWeights`, the level of a page of weight `2^m` is `m`. -/
lemma pageLevel_of_eq {q : Fin n} {m : ℕ} (hm : w q = 2 ^ m) :
    PagingWithDelay.PMD.level I q = m := by
  show Int.clog 2 (w q) = m
  rw [hm, show ((2 : ℝ) ^ m) = ((2 : ℕ) : ℝ) ^ (m : ℤ) by norm_num]
  exact Int.clog_zpow (by norm_num) _

lemma pageLevel_nonneg (q : Fin n) : 0 ≤ PagingWithDelay.PMD.level I q := by
  obtain ⟨m, hm⟩ := hw.1 q
  rw [pageLevel_of_eq hk hkn hw hO₀ hi₀ π hm]
  exact Int.natCast_nonneg m

lemma exists_pageLevel_zero : ∃ q, PagingWithDelay.PMD.level I q = 0 := by
  obtain ⟨q, hq⟩ := hw.2
  exact ⟨q, pageLevel_of_eq (m := 0) hk hkn hw hO₀ hi₀ π (by simpa using hq)⟩

lemma floor_log_eq {m : ℕ} :
    ⌊Real.log (max 1 ((2 : ℝ) ^ m)) / Real.log 2⌋₊ = m := by
  rw [max_eq_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)), Real.log_pow,
    mul_div_assoc, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one,
    Nat.floor_natCast]

/-- With `PMDWeights` (powers `2^m`, `m ≥ 0`, one weight `1`), the lightest level is `0`.

Proof sketch: `level q = Int.clog 2 (2^m) = m ≥ 0` (`Int.clog_zpow` / `Int.clog_natCast` style
lemmas), and the page of weight `1` has level `0`; `⨅` over the nonempty `Fin n` (`n > k ≥ 1`). -/
lemma minLevel_eq : minLevel I = 0 := by
  obtain ⟨q, hq⟩ := exists_pageLevel_zero hk hkn hw hO₀ hi₀ π (σ := σ)
  have : Nonempty (Fin n) := ⟨q⟩
  exact le_antisymm (hq ▸ ciInf_le (Set.finite_range _).bddBelow q)
    (le_ciInf fun i => pageLevel_nonneg hk hkn hw hO₀ hi₀ π i)

lemma maxLevel_nonneg : 0 ≤ maxLevel I := by
  obtain ⟨q, hq⟩ := exists_pageLevel_zero hk hkn hw hO₀ hi₀ π (σ := σ)
  exact hq ▸ le_ciSup (Set.finite_range _).bddAbove q

/-- The platform's levels are ours: `levels w = [0, …, maxLevel]`.

Proof sketch: for `w i = 2^m`, `⌊log (max 1 2^m) / log 2⌋₊ = m = level i`; so the `sup` is the
largest exponent, which is `maxLevel I` (`⨆` of the levels, attained). -/
lemma levels_eq : levels w = List.range ((maxLevel I).toNat + 1) := by
  set f : Fin n → ℕ := fun i => ⌊Real.log (max 1 (w i)) / Real.log 2⌋₊
  have hf : ∀ i, PagingWithDelay.PMD.level I i = f i := fun i => by
    obtain ⟨m, hm⟩ := hw.1 i
    simp only [f, hm, floor_log_eq]
    exact pageLevel_of_eq hk hkn hw hO₀ hi₀ π hm
  obtain ⟨q, -⟩ := hw.2
  have : Nonempty (Fin n) := ⟨q⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
  have hM : maxLevel I = (Finset.univ.sup f : ℕ) := by
    refine le_antisymm (ciSup_le fun j => ?_) ?_
    · rw [hf]; exact_mod_cast Finset.le_sup (Finset.mem_univ j)
    · rw [hi, ← hf]; exact le_ciSup (Set.finite_range _).bddAbove i
  unfold levels
  rw [hM, Int.toNat_natCast, add_comm]

/-- The platform's band length is our `levelLen`. Proof: case split on `S ≤ LW`, `LW ≤ S ≤ 2LW`,
`2LW ≤ S` with `S = serviceEnd ≥ 0` and `L W > 0`. -/
lemma bandLength_eq (x : Fin n → ℝ) (p : Fin n) (j : ℕ) :
    bandLength k (serviceEnd I x p) (level j) = levelLen I x p j := by
  have hL : 0 < logFactor k := Real.log_pos (by norm_cast; omega)
  have hW : 0 < level j := by unfold level; positivity
  unfold bandLength PagingWithDelay.PMD.levelLen
  rw [← levelWeight_natCast, J_L]
  set S := serviceEnd I x p
  set W := levelWeight (j : ℤ)
  have ha : 0 < logFactor k * W := mul_pos hL hW
  rw [show 2 * W * logFactor k = 2 * logFactor k * W by ring, mul_comm W]
  rcases le_total S (logFactor k * W) with h | h
  · rw [min_eq_right h, min_eq_right (by linarith : S ≤ 2 * logFactor k * W), sub_self]
    exact max_eq_left (by linarith)
  · rw [min_eq_left h]
    exact max_eq_right (by
      rcases le_total S (2 * logFactor k * W) with h' | h'
      · rw [min_eq_right h']; linarith
      · rw [min_eq_left h']; linarith)

/-- Deposits: for levels `j ≤ maxLevel` the platform's deposit is ours. -/
lemma deposit_eq (x : Fin n → ℝ) (p : Fin n) (B : ℤ → ℝ) (j : ℕ) (hj : (j : ℤ) ≤ maxLevel I) :
    deposit I x p B j =
      B j + (if w p ≤ level j then bandLength k (serviceEnd I x p) (level j) else 0) := by
  unfold PagingWithDelay.PMD.deposit
  rw [bandLength_eq hk hkn hw hO₀ hi₀ π]
  by_cases h : w p ≤ level j
  · rw [if_pos ⟨(pageLevel_le_iff hk hkn hw hO₀ hi₀ π p j).2 h, hj⟩, if_pos h]
  · rw [if_neg fun h' => h ((pageLevel_le_iff hk hkn hw hO₀ hi₀ π p j).1 h'.1), if_neg h,
      add_zero]

/-! ### Holes -/

lemma mass_eq (j : ℕ) (x : Fin n → ℝ) :
    mass w j x = ∑ i ∈ Finset.univ.filter (fun i => PagingWithDelay.PMD.level I i ≤ j), (1 - x i) := by
  unfold mass
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (pageLevel_le_iff hk hkn hw hO₀ hi₀ π i j).symm

/-- The platform's hole is ours when the condition on the mass holds (then the platform's
`θ = (1-δ)/mass` equals our `holeFraction = min 1 ((1-δ)/mass)`, as `mass ≥ 1 - δ > 0`). -/
lemma openSnap_x {j : ℕ} {e : Execution n} (hm : mass w j e.current.x ≥ 1 - delta k) :
    (openSnap k w j e).x = hole I e.current.x j := by
  have hδ : delta k < 1 := by
    unfold delta
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpos : 0 < mass w j e.current.x := by linarith
  have hθ : (1 - delta k) / mass w j e.current.x ≤ 1 := by
    rw [div_le_one hpos]; linarith
  funext i
  simp only [openSnap, hole, PagingWithDelay.PMD.holeFraction]
  rw [← mass_eq hk hkn hw hO₀ hi₀ π, J_delta, min_eq_right hθ]
  change (if w i ≤ level j then _ + (if mass w j e.current.x = 0 then _ else _) * _ else _) = _
  rw [if_neg hpos.ne']
  by_cases h : w i ≤ level j
  · rw [if_pos h, if_pos ((pageLevel_le_iff hk hkn hw hO₀ hi₀ π i j).2 h)]
    rfl
  · rw [if_neg h, if_neg fun h' => h ((pageLevel_le_iff hk hkn hw hO₀ hi₀ π i j).1 h')]

/-! ### Delays and the trigger -/

/-- **Page delays agree**: the platform's `pageDelay` of `rs` is ours of any permutation of
`rs.map conv`. Proof: `List.Perm.filter`, `List.Perm.map`, `List.Perm.sum_eq`, then
`List.filter_map`, `List.map_map` and `Thm1.conv_delay` (valid requests). -/
lemma pageDelay_eq {rs : Instance n} (hrs : ∀ r ∈ rs, ValidRequest r)
    {P : List (PagingWithDelay.Request (Fin n))} (hP : (rs.map Thm1.conv).Perm P)
    (q : Fin n) (t : ℝ) :
    PagingDelay.PMD.pageDelay rs q t = PagingWithDelay.PMD.pageDelay P q t := by
  unfold PagingDelay.PMD.pageDelay PagingWithDelay.PMD.pageDelay
  rw [← ((hP.filter _).map _).sum_eq, List.filter_map, List.map_map]
  simp only [Function.comp_def, Thm1.conv_page, Thm1.conv_arrival]
  congr 1
  exact List.map_congr_left fun r hr =>
    (Thm1.conv_delay (hrs r (List.mem_of_mem_filter hr)) (t - r.arrival)).symm

/-- The platform's pending requests are valid requests of `σ`. -/
lemma pending_valid (hσ : ValidInstance σ) (e : Execution n) (t : ℝ) :
    ∀ r ∈ pending k e σ t, ValidRequest r := by
  intro r hr
  exact hσ r (List.mem_of_mem_filter hr)

/-- **Overshoots agree.** -/
lemma overshoot_eq (hσ : ValidInstance σ) {e : Execution n} {t : ℝ}
    {P : List (PagingWithDelay.Request (Fin n))}
    (hP : ((pending k e σ t).map Thm1.conv).Perm P) (q : Fin n) :
    PagingDelay.PMD.overshoot k w e σ t q =
      PagingWithDelay.PMD.overshoot I P e.current.claims q t := by
  unfold PagingDelay.PMD.overshoot PagingWithDelay.PMD.overshoot
  rw [pageDelay_eq (pending_valid hσ e t) hP]
  rfl

/-- **The platform's trigger is ours.** -/
lemma criticalAt_iff (hσ : ValidInstance σ) {e : Execution n} {t : ℝ}
    {P : List (PagingWithDelay.Request (Fin n))}
    (hP : ((pending k e σ t).map Thm1.conv).Perm P) (hx : StateValid k e.current.x) (p : Fin n) :
    CriticalAt k w e σ p t ↔
      e.current.time ≤ t ∧ TriggerCond I e.current.x P e.current.claims t p := by
  unfold CriticalAt TriggerCond
  simp only [overshoot_eq hk hkn hw hO₀ hi₀ π hσ hP]
  rw [pathLength_eq' hk hkn hw hO₀ hi₀ π hx]
  rfl

/-- **Deadlines agree** for a page with a pending request: the platform's `effectiveDeadline`
is `some` of our `pageDeadline` (the set is nonempty since delays are unbounded and nonnegative).
-/
lemma effectiveDeadline_eq {rs : Instance n} (hrs : ∀ r ∈ rs, ValidRequest r)
    {P : List (PagingWithDelay.Request (Fin n))} (hP : (rs.map Thm1.conv).Perm P)
    {q : Fin n} (hq : ∃ r ∈ rs, r.page = q) (t : ℝ) :
    effectiveDeadline w rs q t = some (pageDeadline I P t q) := by
  have hS : ∀ u, PagingDelay.PMD.pageDelay rs q u = PagingWithDelay.PMD.pageDelay P q u :=
    fun u => pageDelay_eq hrs hP q u
  unfold effectiveDeadline pageDeadline
  simp only [hS]
  rw [if_pos]
  · rfl
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨τ, hτ⟩ := (Thm1.conv r).delay_unbounded (w r.page + 1)
  refine ⟨max t (r.arrival + τ), le_max_left _ _, ?_⟩
  have hle : (Thm1.conv r).delay τ ≤ (Thm1.conv r).delay (max t (r.arrival + τ) - r.arrival) :=
    (Thm1.conv r).delay_mono (by linarith [le_max_right t (r.arrival + τ)])
  rw [Thm1.conv_delay (hrs r hr), Thm1.conv_delay (hrs r hr)] at hle
  rw [Thm1.conv_delay (hrs r hr)] at hτ
  unfold PagingDelay.PMD.pageDelay
  refine lt_of_lt_of_le (by linarith) (le_trans hle ?_)
  exact List.single_le_sum (fun _ h => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 h; exact NNReal.coe_nonneg _)
    _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simp⟩, rfl⟩)

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Ours` -/
section

/-!
# Simulation bridge: facts about our event loop

Facts about our run (`PagingWithDelay.PMD.log`) for an arbitrary instance on `Fin n`, used by the
simulation:

* `tail input l`: the platform moves recorded by the log entries from index `l` on;
* `critCount input l`: the number of critical services from index `l` on, and its bound by the
  number of requests (the platform's fuel);
* the shape of the log: idle segments (ticks and advances up to the next critical service or the
  end), the examination of a level, the steps of a preemptive service;
* arrivals: every arrival time is either reached or still upcoming.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage next_snapAt inv_snapAt
  tripCandidate levelWeight afterLevel preemptCondition triggerTimes)

variable {n : ℕ} (input : PagingWithDelay.Instance (Fin n))

/-! ### The recorded moves from an index on -/

/-- The platform moves (as views) recorded by the log entries from index `l` on. -/
def tail (l : ℕ) : List (MoveKind n × (Fin n → ℝ) × (Fin n → ℝ) × ℝ) :=
  ((log input).drop l).flatMap fun en => entryMoves input en.1 en.2

/-- Whether a move of our loop is a critical service. -/
def isCritical : PagingWithDelay.PMD.Move (Fin n) → Bool
  | .critical _ => true
  | _ => false

/-- The number of critical services from index `l` on. -/
def critCount (l : ℕ) : ℕ :=
  ((log input).drop l).countP fun en => isCritical en.2

variable {input}

lemma tail_zero : tail input 0 = logMoves input := by
  simp [tail, logMoves]

lemma tail_length : tail input (log input).length = [] := by
  simp [tail]

lemma tail_succ {l : ℕ} (h : l < (log input).length) :
    tail input l = entryMoves input (snapAt input l) (moveAt l h) ++ tail input (l + 1) := by
  unfold tail
  rw [List.drop_eq_getElem_cons h, List.flatMap_cons,
    PagingWithDelay.PMD.log_getElem (input := input) l h]

lemma critCount_succ {l : ℕ} (h : l < (log input).length) :
    critCount input l = (if isCritical (moveAt l h) then 1 else 0) + critCount input (l + 1) := by
  unfold critCount
  rw [List.drop_eq_getElem_cons h, List.countP_cons,
    PagingWithDelay.PMD.log_getElem (input := input) l h]
  simp only
  split_ifs <;> omega

lemma critCount_succ_of_not {l : ℕ} (h : l < (log input).length)
    (hm : ∀ p, moveAt l h ≠ .critical p) : critCount input l = critCount input (l + 1) := by
  rw [critCount_succ h]
  have : isCritical (moveAt l h) = false := by
    cases hc : moveAt l h <;> simp [isCritical]
    exact hm _ hc
  simp [this]

lemma critCount_succ_of_critical {l : ℕ} (h : l < (log input).length) {p : Fin n}
    (hm : moveAt l h = .critical p) : critCount input l = critCount input (l + 1) + 1 := by
  rw [critCount_succ h, hm]
  simp [isCritical]
  omega

variable (input) in
/-- The potential of `critCount_le`: pending requests plus requests still to arrive. -/
def oursPhi (l : ℕ) : ℕ := (snapAt input l).pending.length +
  input.requests.countP (fun ρ => decide (ρ.arrival ∈ (snapAt input l).upcoming))

lemma oursPhi_step {l : ℕ} (h : l < (log input).length) :
    (if isCritical (moveAt l h) then 1 else 0) + oursPhi input (l + 1) ≤ oursPhi input l := by
  have hv := input.valid
  unfold oursPhi
  by_cases ht : ∃ t, moveAt l h = .tick t
  · obtain ⟨t, ht⟩ := ht
    obtain ⟨-, -, -, hup, heq⟩ := PagingWithDelay.PMD.tick_spec hv h ht
    have hnot : t ∉ (snapAt input (l + 1)).upcoming := by
      have hp := PagingWithDelay.PMD.upcoming_pairwise hv l
      rw [hup, List.pairwise_cons] at hp
      exact fun hm => lt_irrefl t (hp.1 t hm)
    have h1 : (snapAt input (l + 1)).pending.length ≤ (snapAt input l).pending.length +
        (input.requests.filter fun ρ => decide (ρ.arrival = t)).length := by
      rw [heq]
      exact (List.length_filter_le _ _).trans (List.length_append ..).le
    rw [hup, PagingWithDelay.PMD.countP_mem_cons _ hnot, ht]
    simp only [isCritical, Bool.false_eq_true, ↓reduceIte, zero_add]
    omega
  · push Not at ht
    rw [PagingWithDelay.PMD.upcoming_succ_of_not_tick hv h ht]
    suffices (if isCritical (moveAt l h) then 1 else 0) + (snapAt input (l + 1)).pending.length ≤
        (snapAt input l).pending.length by omega
    rcases hm : moveAt l h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    · exact absurd hm (ht t)
    · rw [PagingWithDelay.PMD.pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm])
        (by simp [hm])]
      simp [isCritical]
    · obtain ⟨-, ⟨ρ, hρ, hρp⟩, -⟩ := PagingWithDelay.PMD.critical_facts hv h hm
      rw [(PagingWithDelay.PMD.critical_spec hv h hm).2.2]
      have : ((snapAt input l).pending.filter (fun π => decide (π.page ≠ p))).length <
          (snapAt input l).pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨ρ, hρ, by simp [hρp]⟩
      simp only [isCritical, ↓reduceIte]
      omega
    · rw [PagingWithDelay.PMD.pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm])
        (by simp [hm])]
      simp [isCritical]
    · rw [PagingWithDelay.PMD.pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm])
        (by simp [hm])]
      simp [isCritical]
    · rw [(PagingWithDelay.PMD.trip_spec hv h hm).2.2.2]
      simp only [isCritical, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact List.length_filter_le _ _
    · rw [PagingWithDelay.PMD.pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm])
        (by simp [hm])]
      simp [isCritical]

lemma critCount_le_oursPhi (l : ℕ) : critCount input l ≤ oursPhi input l := by
  by_cases h : l < (log input).length
  · rw [critCount_succ h]
    have := critCount_le_oursPhi (l + 1)
    have := oursPhi_step h
    omega
  · simp [critCount, List.drop_eq_nil_of_le (by omega : (log input).length ≤ l)]
termination_by (log input).length - l
decreasing_by omega

/-- **Fuel bound**: there are at most as many critical services as requests.

Proof sketch: `Φ l = (snapAt l).pending.length + #{ρ ∈ requests | ρ.arrival ∈ (snapAt l).upcoming}`
is `requests.length` at `0` (`initialSnap`: no pending, `upcoming = arrivalTimes`), never increases
(a tick at `t` moves the requests arriving at `t` from the second count into `pending` or drops
them; trips and critical services only filter `pending`; the other moves change neither), and
drops by at least one at a critical service (the critical page has a pending request,
`Inv.exists_pending_of_triggerPage`, which is filtered out). Hence
`critCount l + Φ l ≤ requests.length` by downward induction, or `critCount l ≤ Φ l`. -/
lemma critCount_le : critCount input 0 ≤ input.requests.length := by
  have h := critCount_le_oursPhi (input := input) 0
  unfold oursPhi at h
  rw [PagingWithDelay.PMD.snapAt_zero input.valid] at h
  have h0 : (PagingWithDelay.PMD.initialSnap input).pending.length = 0 := rfl
  have h1 : input.requests.countP (fun ρ => decide (ρ.arrival ∈
      (PagingWithDelay.PMD.initialSnap input).upcoming)) = input.requests.length :=
    List.countP_eq_length.mpr (fun ρ hρ => by
      simpa [PagingWithDelay.PMD.initialSnap] using PagingWithDelay.PMD.arrival_mem_arrivalTimes hρ)
  omega

/-! ### The shape of the log -/

/-- If the log is empty, there are no requests (otherwise the first arrival is ticked).

Proof sketch: `next_final` at `0 = log.length`, `next_eq_none` gives `upcoming = []` for the
initial snapshot, i.e. `arrivalTimes = []`, so no request (`arrival_mem_arrivalTimes`). -/
lemma requests_eq_nil_of_log (hl : log input = []) : input.requests = [] := by
  have hv := input.valid
  have h0 := (PagingWithDelay.PMD.final_spec hv).1
  rw [hl, List.length_nil, PagingWithDelay.PMD.snapAt_zero hv] at h0
  change PagingWithDelay.PMD.arrivalTimes input = [] at h0
  rw [List.eq_nil_iff_forall_not_mem]
  intro ρ hρ
  have := PagingWithDelay.PMD.arrival_mem_arrivalTimes hρ
  rw [h0] at this
  simp at this

/-- The first move is a tick, after which the loop is idle. -/
lemma first_tick_idle (h : 0 < (log input).length) :
    (∃ t, moveAt 0 h = .tick t) ∧ (snapAt input 1).stage = .idle := by
  obtain ⟨t, ht⟩ := PagingWithDelay.PMD.first_tick input.valid h
  refine ⟨⟨t, ht⟩, ?_⟩
  obtain ⟨hst, -, -, -, heq⟩ := PagingWithDelay.PMD.tick_spec input.valid h ht
  rw [heq]
  exact hst

/-- **Idle segment.** From an idle index, the loop makes ticks and advances until it reaches the
end of the log or a critical service.

Proof sketch: let `j` be the least `l ≥ i` with `l = log.length` or `moveAt l` neither a tick nor
an advance (`Nat.find`). Ticks and advances keep the stage idle (`tick_spec`, `advance_spec`), so
`snapAt j` is idle; if `j < log.length`, `next` from an idle state that is neither tick nor
advance is a critical service (`Run/Step.lean`, `next_*`: every other move needs a non-idle
stage). -/
lemma idle_segment {i : ℕ} (hi : i ≤ (log input).length) (hst : (snapAt input i).stage = .idle) :
    ∃ j, i ≤ j ∧ j ≤ (log input).length ∧
      (∀ l (h : l < (log input).length), i ≤ l → l < j →
        (∃ t, moveAt l h = .tick t) ∨ (∃ t, moveAt l h = .advance t)) ∧
      (snapAt input j).stage = .idle ∧
      (j = (log input).length ∨ ∃ (h : j < (log input).length) (p : Fin n),
        moveAt j h = .critical p) := by
  have hv := input.valid
  obtain ⟨d, hd⟩ : ∃ d, d = (log input).length - i := ⟨_, rfl⟩
  induction d generalizing i with
  | zero =>
    exact ⟨i, le_rfl, hi, fun l h h1 h2 => absurd h2 (by omega), hst, Or.inl (by omega)⟩
  | succ d ih =>
    have hlt : i < (log input).length := by omega
    by_cases hta : (∃ t, moveAt i hlt = .tick t) ∨ (∃ t, moveAt i hlt = .advance t)
    · have hst' : (snapAt input (i + 1)).stage = .idle := by
        rcases hta with ⟨t, hm⟩ | ⟨t, hm⟩
        · rw [(PagingWithDelay.PMD.tick_spec hv hlt hm).2.2.2.2]; exact hst
        · rw [(PagingWithDelay.PMD.advance_spec hv hlt hm).2.2.2.2.2.2]; exact hst
      obtain ⟨j, hij, hj, hseg, hjst, hend⟩ := ih (by omega) hst' (by omega)
      refine ⟨j, by omega, hj, fun l h h1 h2 => ?_, hjst, hend⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact hta
      · exact hseg l h (by omega) h2
    rcases hm : moveAt i hlt with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    · simp [hm] at hta
    · simp [hm] at hta
    · exact ⟨i, le_rfl, hi, fun l h h1 h2 => absurd h2 (by omega), hst, Or.inr ⟨hlt, p, hm⟩⟩
    · have := (PagingWithDelay.PMD.skip_spec hv hlt hm).1; rw [hst] at this; cases this
    · have := (PagingWithDelay.PMD.openHole_spec hv hlt hm).1; rw [hst] at this; cases this
    · obtain ⟨⟨b, hb⟩, -⟩ := PagingWithDelay.PMD.trip_spec hv hlt hm; rw [hst] at hb; cases hb
    · obtain ⟨b, hb, -⟩ := PagingWithDelay.PMD.closeHole_spec hv hlt hm; rw [hst] at hb; cases hb

/-- The examination of level `e`: a skip or the opening of a hole. -/
lemma examine_step {l : ℕ} {e : ℤ} (hst : (snapAt input l).stage = .examine e) :
    ∃ h : l < (log input).length, moveAt l h = .skip e ∨ moveAt l h = .openHole e := by
  have hlt := PagingWithDelay.PMD.lt_length_of_stage input.valid (l := l) (by rw [hst]; simp)
  refine ⟨hlt, ?_⟩
  rcases PagingWithDelay.PMD.next_of_examine hst (next_snapAt input.valid l hlt) with
    ⟨hm, -⟩ | ⟨hm, -⟩
  · exact Or.inl hm
  · exact Or.inr hm

/-- A step inside a level-`e` preemptive service: a round trip on the candidate if the budget
allows it, otherwise the hole is closed.

Proof sketch: `lt_length_of_stage`, `next_of_preempt` (trip or close), then `trip_spec` /
`closeHole_spec` for the conditions; in the trip case the stage stays `preempt e b`. -/
lemma preempt_step {l : ℕ} {e : ℤ} {b : Fin n → ℝ} (hst : (snapAt input l).stage = .preempt e b) :
    ∃ h : l < (log input).length,
      (tripCandidate input (snapAt input l).pending (snapAt input l).now e = none ∧
          moveAt l h = .closeHole e none) ∨
      (∃ ρ, tripCandidate input (snapAt input l).pending (snapAt input l).now e = some ρ ∧
          levelWeight e ≤ (snapAt input l).budget e ∧ moveAt l h = .trip e ρ ∧
          (snapAt input (l + 1)).stage = .preempt e b) ∨
      (∃ ρ, tripCandidate input (snapAt input l).pending (snapAt input l).now e = some ρ ∧
          (snapAt input l).budget e < levelWeight e ∧ moveAt l h = .closeHole e (some ρ)) := by
  have hv := input.valid
  have hlt := PagingWithDelay.PMD.lt_length_of_stage hv (l := l) (by rw [hst]; simp)
  refine ⟨hlt, ?_⟩
  rcases PagingWithDelay.PMD.next_of_preempt hst (next_snapAt hv l hlt) with
    ⟨ρ, hm, hst'⟩ | ⟨stop, hm, -⟩
  · obtain ⟨-, hc, hb, -⟩ := PagingWithDelay.PMD.trip_spec hv hlt hm
    exact Or.inr (Or.inl ⟨ρ, hc, hb, hm, hst'⟩)
  · obtain ⟨b', -, hc, -⟩ := PagingWithDelay.PMD.closeHole_spec hv hlt hm
    cases stop with
    | none => exact Or.inl ⟨hc, hm⟩
    | some ρ => exact Or.inr (Or.inr ⟨ρ, hc.1, hc.2, hm⟩)

/-! ### Arrivals -/

/-- Every arrival time has been reached or is still upcoming.

Proof sketch: induction on `l`. At `0`, `upcoming = arrivalTimes` (`arrival_mem_arrivalTimes`).
A tick at `t` removes `t` from `upcoming` and sets `now := t`; the other moves keep `upcoming`
and do not decrease `now` (`now_succ`). Past the end of the log `snapAt` is constant. -/
lemma arrival_le_now_or_mem_upcoming {ρ : PagingWithDelay.Request (Fin n)}
    (hρ : ρ ∈ input.requests) (l : ℕ) :
    ρ.arrival ≤ (snapAt input l).now ∨ ρ.arrival ∈ (snapAt input l).upcoming := by
  have hv := input.valid
  induction l with
  | zero =>
    right; rw [PagingWithDelay.PMD.snapAt_zero hv]
    exact PagingWithDelay.PMD.arrival_mem_arrivalTimes hρ
  | succ l ih =>
    by_cases hl : l < (log input).length
    · have hnow := PagingWithDelay.PMD.now_succ hv l
      by_cases ht : ∃ t, moveAt l hl = .tick t
      · obtain ⟨t, ht⟩ := ht
        obtain ⟨-, -, -, hup, heq⟩ := PagingWithDelay.PMD.tick_spec hv hl ht
        rcases ih with h | h
        · exact Or.inl (h.trans hnow)
        · rw [hup] at h
          rcases List.mem_cons.mp h with h | h
          · left; rw [heq]; exact h.le
          · exact Or.inr h
      · push Not at ht
        rw [PagingWithDelay.PMD.upcoming_succ_of_not_tick hv hl ht]
        exact ih.imp_left (fun h => h.trans hnow)
    · rw [PagingWithDelay.PMD.snapAt_of_ge (by omega : (log input).length ≤ l + 1)]
      rw [PagingWithDelay.PMD.snapAt_of_ge (by omega)] at ih
      exact ih

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Rel` -/
section

/-!
# Simulation bridge: the simulation relation and the idle phase

`Rel e l` relates a platform execution `e` to our loop state `snapAt J l` (for `l ≥ 1`, after the
first tick): same fractional state, claims and budgets (levels `≤ maxLevel`; the platform's
budgets above `maxLevel` are only nonnegative), the platform's trace is chained and its moves end
by `e.current.time ≤ now`, no page is critical for the platform in `[e.current.time, now)`, and the
platform's pending requests at any time in `[now, next arrival)` are ours.

The idle phase (ticks and advances) does not change `e` and records no platform move:
`rel_tick`, `rel_advance`, and `idle_phase` (assembled here).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage maxLevel)

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

variable (σ) in
/-- **The simulation relation** between the platform execution `e` and our state `snapAt J l`. -/
structure Rel (e : Execution n) (l : ℕ) : Prop where
  pos : 1 ≤ l
  x : e.current.x = (snapAt I l).x
  claims : e.current.claims = (snapAt I l).claims
  budget : ∀ j : ℕ, (j : ℤ) ≤ maxLevel I → e.current.budget j = (snapAt I l).budget j
  budget_hi : ∀ j : ℕ, maxLevel I < j → 0 ≤ e.current.budget j
  moves_budget : ∀ m ∈ e.moves, ∀ j, 0 ≤ m.after.budget j
  chain : Chain e
  moves_time : ∀ m ∈ e.moves, m.after.time ≤ e.current.time
  time : e.current.time ≤ (snapAt I l).now
  quiet : ∀ p t, e.current.time ≤ t → t < (snapAt I l).now → ¬ CriticalAt k w e σ p t
  pend : ∀ t, (snapAt I l).now ≤ t → (∀ a ∈ (snapAt I l).upcoming, t < a) →
    ((pending k e σ t).map Thm1.conv).Perm (snapAt I l).pending

/-! ### Helpers -/

lemma filter_or_perm {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) :
    (l.filter (fun x => p x || q x)).Perm (l.filter p ++ l.filter q) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    cases hp : p x <;> cases hq : q x <;> simp only [List.filter_cons, hp, hq, Bool.or_self,
      Bool.or_true, Bool.true_or, if_true, List.cons_append] <;>
      simp_all
    exact (ih.cons x).trans List.perm_middle.symm

lemma map_conv_filter (σ : Instance n) (a : ℝ) (x : Fin n → ℝ) (d : ℝ) :
    (σ.filter (fun r => decide (r.arrival = a ∧ x r.page ≠ d))).map Thm1.conv =
      ((σ.map Thm1.conv).filter (fun ρ => decide (ρ.arrival = a))).filter
        (fun ρ => decide (x ρ.page ≠ d)) := by
  rw [List.filter_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro r _
  simp [Bool.and_comm]

lemma pending_nil_of {k : ℕ} {e : Execution n} {a τ : ℝ} (ha : ∀ r ∈ σ, a ≤ r.arrival)
    (hτ : τ < a) : pending k e σ τ = [] := by
  unfold pending
  rw [List.filter_eq_nil_iff]
  intro r hr
  have := ha r hr
  simp only [decide_eq_true_eq, not_and]
  intro h; linarith

/-- The platform's pending requests after the arrivals at `a`: the old ones plus the fresh ones
whose page is not at `δ`. -/
lemma pend_tick {k : ℕ} {e : Execution n} (hc : Chain e) {t₀ a t : ℝ}
    {P : List (PagingWithDelay.Request (Fin n))} (hP : ((pending k e σ t₀).map Thm1.conv).Perm P)
    (hPx : ∀ ρ ∈ P, e.current.x ρ.page ≠ delta k)
    (hmv : ∀ m ∈ e.moves, m.after.time < a) (h0 : t₀ < a) (hat : a ≤ t)
    (hdich : ∀ r ∈ σ, r.arrival ≤ t → r.arrival ≤ t₀ ∨ r.arrival = a) :
    ((pending k e σ t).map Thm1.conv).Perm
      ((P ++ (σ.map Thm1.conv).filter (fun ρ => decide (ρ.arrival = a))).filter
        (fun ρ => decide (e.current.x ρ.page ≠ delta k))) := by
  have hsplit : (pending k e σ t).Perm (pending k e σ t₀ ++
      σ.filter (fun r => decide (r.arrival = a ∧ e.current.x r.page ≠ delta k))) := by
    unfold pending
    rw [List.filter_congr (q := fun r => decide (r.arrival ≤ t₀ ∧ fractionalService k e r = none)
      || decide (r.arrival = a ∧ e.current.x r.page ≠ delta k))]
    · refine filter_or_perm _ _ _ fun r hr h => ?_
      simp only [decide_eq_true_eq] at h
      linarith [h.1.1, h.2.1]
    · intro r hr
      by_cases h1 : r.arrival ≤ t₀
      · have : r.arrival ≠ a := by intro h; linarith
        simp [h1, this, h1.trans (by linarith : t₀ ≤ t)]
      · by_cases h2 : r.arrival ≤ t
        · have har : r.arrival = a := (hdich r hr h2).resolve_left h1
          rw [fractionalService_fresh k hc (fun m hm => har ▸ hmv m hm)]
          by_cases hx : e.current.x r.page = delta k <;> simp [har, hx, hat]
        · have : r.arrival ≠ a := by intro h; exact h2 (h ▸ hat)
          simp [h1, h2, this]
  rw [List.filter_append, List.filter_eq_self.2 (fun ρ hρ => by simpa using hPx ρ hρ),
    ← map_conv_filter]
  refine (hsplit.map _).trans ?_
  rw [List.map_append]
  exact hP.append_right _

/-- In the idle phase, no page is critical for the platform in `[now, entryTime)` (before the
next upcoming arrival). -/
lemma quiet_step (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length)
    (hm : (∃ t, moveAt l h = .tick t) ∨ (∃ t, moveAt l h = .advance t))
    (hup : ∀ a ∈ (snapAt I l).upcoming, PagingWithDelay.PMD.entryTime I l ≤ a)
    (p : Fin n) (τ : ℝ) (h1 : e.current.time ≤ τ) (h2 : τ < PagingWithDelay.PMD.entryTime I l) :
    ¬ CriticalAt k w e σ p τ := by
  by_cases hτ : τ < (snapAt I l).now
  · exact hR.quiet p τ h1 hτ
  rw [not_lt] at hτ
  have hv := (I).valid
  have hst : (snapAt I l).stage = .idle := by
    rcases hm with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact (PagingWithDelay.PMD.tick_spec hv h ht).1
    · exact (PagingWithDelay.PMD.advance_spec hv h ht).1
  have hx : StateValid k e.current.x := by
    rw [← isRest_iff' hk hkn hw hO₀ hi₀ π, hR.x,
      PagingWithDelay.PMD.x_eq_baseState hv (fun _ _ h' => by rw [hst] at h'; cases h')]
    exact PagingWithDelay.PMD.baseState_isRest hv l
  have hP := hR.pend τ hτ (fun a ha => lt_of_lt_of_le h2 (hup a ha))
  rw [criticalAt_iff hk hkn hw hO₀ hi₀ π hσ hP hx]
  rintro ⟨-, hT⟩
  rw [hR.x, hR.claims] at hT
  exact PagingWithDelay.PMD.not_triggered_before hv h hm hτ h2 p hT

/-- **Start.** After our first tick (at the first arrival `a₁ ≥ 0`), the platform's start is
related to index `1`.

Proof sketch: `snapAt 1` is the tick at `a₁` from `initialSnap` (`first_tick`, `tick_spec`):
`x = initialState = initialX` (`initialX_eq`-style computation `(k+1)δ = 1 - kδ`), claims and
budgets `0`, `now = a₁`. No moves, so `Chain`, `moves_*` are trivial; `time : 0 ≤ a₁` from
`ValidRequest`. `quiet`: for `t < a₁` no request has arrived (`a₁` is the least arrival,
`arrivalTimes` sorted), so `pending = []` and every overshoot is `max 0 (0 - 0 - w) = 0`.
`pend`: for `t ∈ [a₁, a₂)` the platform's pending requests are those arriving at `a₁` whose page
is not at `δ` in `initialX` (`fractionalService_fresh` with no moves), which is our tick's filter
(`List.filter_map`, `Thm1.conv_arrival`, `Thm1.conv_page`). -/
lemma rel_one (hσ : ValidInstance σ) (h : 0 < (log I).length) :
    Rel hk hkn hw hO₀ hi₀ π σ (start k O₀ i₀) 1 := by
  have hv := (I).valid
  obtain ⟨a, ha⟩ := PagingWithDelay.PMD.first_tick hv h
  obtain ⟨-, -, -, hup, heq⟩ := PagingWithDelay.PMD.tick_spec hv h ha
  rw [PagingWithDelay.PMD.snapAt_zero hv] at hup heq
  change PagingWithDelay.PMD.arrivalTimes I = a :: (snapAt I 1).upcoming at hup
  have hpw := hup ▸ PagingWithDelay.PMD.arrivalTimes_pairwise (input := I)
  have hmem : ∀ r ∈ σ, r.arrival ∈ a :: (snapAt I 1).upcoming := fun r hr => by
    rw [← hup]
    simpa using PagingWithDelay.PMD.arrival_mem_arrivalTimes (input := I)
      (List.mem_map_of_mem hr : Thm1.conv r ∈ (I).requests)
  have hge : ∀ r ∈ σ, a ≤ r.arrival := fun r hr => by
    rcases List.mem_cons.1 (hmem r hr) with h' | h'
    · exact h'.ge
    · exact (List.rel_of_pairwise_cons hpw h').le
  have ha0 : 0 ≤ a := by
    have : a ∈ PagingWithDelay.PMD.arrivalTimes I := by rw [hup]; exact List.mem_cons_self
    simp only [PagingWithDelay.PMD.arrivalTimes, Finset.mem_sort, List.mem_toFinset,
      List.mem_map] at this
    obtain ⟨ρ, hρ, rfl⟩ := this
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (show ρ ∈ σ.map Thm1.conv from hρ)
    simpa using (hσ r hr).1
  have hnow : (snapAt I 1).now = a := by rw [heq]
  have hx : (start k O₀ i₀).current.x = (snapAt I 1).x := by
    rw [heq]
    funext i
    show (if i ∈ O₀ then delta k else if i = i₀ then ((k : ℝ) + 1) * delta k else 1) =
      (if i ∈ O₀ then delta k else if some i₀ = some i then 1 - (k : ℝ) * delta k else 1)
    by_cases h1 : i ∈ O₀
    · simp [h1]
    · by_cases h2 : i = i₀
      · subst h2
        simp only [h1, if_false, if_true, delta]
        field_simp
        ring
      · simp [h1, h2, Ne.symm h2]
  refine ⟨le_rfl, hx, by rw [heq]; rfl, fun j _ => by rw [heq]; rfl, fun j _ => le_rfl,
    by simp [start], chain_start k O₀ i₀, by simp [start], by rw [hnow]; exact ha0, ?_, ?_⟩
  · intro p τ h1 h2
    rw [hnow] at h2
    have hwp := Bridge.weight_pos_of_PMDWeights hw p
    unfold CriticalAt PagingDelay.PMD.overshoot
    rw [pending_nil_of hge h2]
    simp [PagingDelay.PMD.pageDelay, start, hwp.le]
  · intro t ht hup'
    rw [hnow] at ht
    have hpend : (snapAt I 1).pending = ([] ++ (σ.map Thm1.conv).filter
        (fun ρ : PagingWithDelay.Request (Fin n) => decide (ρ.arrival = a))).filter
          (fun ρ => decide ((start k O₀ i₀).current.x ρ.page ≠ delta k)) := by
      rw [hx, heq]; rfl
    rw [hpend]
    refine pend_tick (chain_start k O₀ i₀) (t₀ := a - 1)
      (by rw [pending_nil_of hge (by linarith)]; simp) (by simp) (by simp [start])
      (by linarith) ht fun r hr hrt => Or.inr ?_
    rcases List.mem_cons.1 (hmem r hr) with h' | h'
    · exact h'
    · exact absurd hrt (not_le.2 (hup' _ h'))

/-- **A tick** keeps the relation (with the same platform execution).

Proof sketch: `tick_spec`; `x`, claims, budgets unchanged. `time`: `now` grows. `quiet` on
`[now, a)`: there `pending k e σ t` is ours (`pend`, as `a` is the head of the sorted `upcoming`),
so `criticalAt_iff` turns `CriticalAt` into `TriggerCond` for `snapAt l`, excluded by
`not_triggered_before`. `pend` at `t ∈ [a, a')`: requests arriving `≤ old now` keep their status
(`pending_eq_of_no_arrival` from `old now` to `t`, minus/plus the arrivals at `a`); the requests
arriving at `a` are fresh (all moves end `≤ e.current.time ≤ old now < a`, `Started`), so by
`fractionalService_fresh` they are pending iff `e.current.x page ≠ δ`, which is our tick's filter;
old pending requests have `x ≠ δ` (`delta_lt_of_pending`), so the filter keeps them. Requests
with arrival in `(old now, a)` or `(a, a')` do not exist (`arrival_le_now_or_mem_upcoming`). -/
lemma rel_tick (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {a : ℝ}
    (hm : moveAt l h = .tick a) : Rel hk hkn hw hO₀ hi₀ π σ e (l + 1) := by
  have hv := (I).valid
  obtain ⟨hst, -, -, hup, heq⟩ := PagingWithDelay.PMD.tick_spec hv h hm
  have hnow : (snapAt I (l + 1)).now = a := by rw [heq]
  have hent : PagingWithDelay.PMD.entryTime I l = a := PagingWithDelay.PMD.entryTime_tick hv h hm
  have hstart : ∀ a' ∈ (snapAt I l).upcoming, (snapAt I l).now < a' :=
    fun a' ha' => PagingWithDelay.PMD.now_lt_upcoming hv h.le hR.pos ha'
  have hlt : (snapAt I l).now < a := hstart a (by rw [hup]; exact List.mem_cons_self)
  have hpw := PagingWithDelay.PMD.upcoming_pairwise hv l
  rw [hup] at hpw
  have hge : ∀ a' ∈ (snapAt I l).upcoming, PagingWithDelay.PMD.entryTime I l ≤ a' := by
    intro a' ha'
    rw [hup] at ha'
    rw [hent]
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hpw ha').le
  refine ⟨by omega, by rw [heq]; exact hR.x, by rw [heq]; exact hR.claims,
    fun j hj => by rw [heq]; exact hR.budget j hj, hR.budget_hi, hR.moves_budget, hR.chain,
    hR.moves_time, by rw [hnow]; exact hR.time.trans hlt.le, ?_, ?_⟩
  · intro p τ h1 h2
    rw [hnow, ← hent] at h2
    exact quiet_step hk hkn hw hO₀ hi₀ π hσ hR h (Or.inl ⟨a, hm⟩) hge p τ h1 h2
  · intro t ht hup'
    rw [hnow] at ht
    have hpend : (snapAt I (l + 1)).pending = ((snapAt I l).pending ++ (σ.map Thm1.conv).filter
        (fun ρ : PagingWithDelay.Request (Fin n) => decide (ρ.arrival = a))).filter
          (fun ρ => decide (e.current.x ρ.page ≠ delta k)) := by
      rw [heq, hR.x]; rfl
    rw [hpend]
    refine pend_tick hR.chain (hR.pend _ le_rfl hstart) ?_
      (fun m hm => (hR.moves_time m hm).trans_lt (hR.time.trans_lt hlt)) hlt ht ?_
    · intro ρ hρ
      rw [hR.x]
      exact (PagingWithDelay.PMD.delta_lt_of_pending hv hρ).ne'
    · intro r hr hrt
      rcases arrival_le_now_or_mem_upcoming (input := I)
          (List.mem_map_of_mem hr : Thm1.conv r ∈ (I).requests) l with h' | h'
      · left; simpa using h'
      · rw [hup] at h'
        rcases List.mem_cons.1 h' with h' | h'
        · right; simpa using h'
        · exact absurd hrt (not_le.2 (by simpa using hup' _ h'))

/-- **An advance** keeps the relation.

Proof sketch: `advance_spec`: only `now` changes, to `t = sInf triggerTimes < next arrival`.
`quiet` on `[old now, t)`: `pend` + `criticalAt_iff` + `not_triggered_before`. `pend` on
`[t, next arrival)`: from the old `pend` (same pending list and upcoming). -/
lemma rel_advance (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {t : ℝ}
    (hm : moveAt l h = .advance t) : Rel hk hkn hw hO₀ hi₀ π σ e (l + 1) := by
  have hv := (I).valid
  obtain ⟨-, -, -, -, -, hlt, heq⟩ := PagingWithDelay.PMD.advance_spec hv h hm
  have hnow : (snapAt I (l + 1)).now = t := by rw [heq]
  have hent : PagingWithDelay.PMD.entryTime I l = t :=
    (PagingWithDelay.PMD.entryTime_advance hv h hm).1
  have hupc : (snapAt I (l + 1)).upcoming = (snapAt I l).upcoming := by rw [heq]
  have hpend : (snapAt I (l + 1)).pending = (snapAt I l).pending := by rw [heq]
  have hge : ∀ a ∈ (snapAt I l).upcoming, PagingWithDelay.PMD.entryTime I l ≤ a :=
    fun a ha => PagingWithDelay.PMD.now_le_upcoming hv (l + 1) (hupc ▸ ha)
  refine ⟨by omega, by rw [heq]; exact hR.x, by rw [heq]; exact hR.claims,
    fun j hj => by rw [heq]; exact hR.budget j hj, hR.budget_hi, hR.moves_budget, hR.chain,
    hR.moves_time, by rw [hnow]; exact hR.time.trans hlt.le, ?_, ?_⟩
  · intro p τ h1 h2
    rw [hnow, ← hent] at h2
    exact quiet_step hk hkn hw hO₀ hi₀ π hσ hR h (Or.inr ⟨t, hm⟩) hge p τ h1 h2
  · intro τ hτ hup'
    rw [hpend]
    rw [hupc] at hup'
    rw [hnow] at hτ
    exact hR.pend τ (hlt.le.trans hτ) hup'

lemma entryMoves_tick (s : Snap (Fin n)) (t : ℝ) : entryMoves I s (.tick t) = [] := rfl
lemma entryMoves_advance (s : Snap (Fin n)) (t : ℝ) : entryMoves I s (.advance t) = [] := rfl

/-- **The idle phase**: ticks and advances up to the next critical service or the end of the log
keep the relation and record no platform move. -/
lemma idle_phase (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) (hi : i ≤ (log I).length)
    (hst : (snapAt I i).stage = .idle) :
    ∃ j, i ≤ j ∧ j ≤ (log I).length ∧ Rel hk hkn hw hO₀ hi₀ π σ e j ∧
      (snapAt I j).stage = .idle ∧ tail I i = tail I j ∧ critCount I i = critCount I j ∧
      (j = (log I).length ∨ ∃ (h : j < (log I).length) (p : Fin n), moveAt j h = .critical p) := by
  obtain ⟨j, hij, hjl, hmoves, hjst, hend⟩ := idle_segment hi hst
  have key : ∀ l, i ≤ l → l ≤ j →
      Rel hk hkn hw hO₀ hi₀ π σ e l ∧ tail I i = tail I l ∧ critCount I i = critCount I l := by
    intro l hl1 hl2
    induction l, hl1 using Nat.le_induction with
    | base => exact ⟨hR, rfl, rfl⟩
    | succ l hil ih =>
      obtain ⟨hRl, htl, hcl⟩ := ih (by omega)
      have hlt : l < (log I).length := by omega
      rcases hmoves l hlt hil (by omega) with ⟨t, ht⟩ | ⟨t, ht⟩
      · refine ⟨rel_tick hk hkn hw hO₀ hi₀ π hσ hRl hlt ht, ?_, ?_⟩
        · rw [htl, tail_succ hlt, ht, entryMoves_tick, List.nil_append]
        · rw [hcl, critCount_succ_of_not hlt (by rw [ht]; simp)]
      · refine ⟨rel_advance hk hkn hw hO₀ hi₀ π hσ hRl hlt ht, ?_, ?_⟩
        · rw [htl, tail_succ hlt, ht, entryMoves_advance, List.nil_append]
        · rw [hcl, critCount_succ_of_not hlt (by rw [ht]; simp)]
  obtain ⟨hRj, htj, hcj⟩ := key j hij le_rfl
  exact ⟨j, hij, hjl, hRj, hjst, htj, hcj, hend⟩

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Next` -/
section

/-!
# Simulation bridge: the platform's next event

At an idle index `i` related to `e`, the platform's `nextEvent` is our next critical service
(time `now`, page `triggerPage`), or `none` at the end of our log.

The per-page facts (`nextPageTime_ge`, `nextPageTime_eq_now_iff`, `nextPageTime_eq_none`) carry
the analysis; `nextEvent_of_critical` and `nextEvent_of_final` assemble them with the list lemmas
of `Platform.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage Critical triggerPage triggerTimes)

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

/-- A gap above `c` below all elements of a list lying strictly above `c`. -/
lemma exists_gap (l : List ℝ) (c : ℝ) (h : ∀ a ∈ l, c < a) : ∃ η > 0, ∀ a ∈ l, c + η ≤ a := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b l ih =>
    obtain ⟨η, hη, hl⟩ := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hb := h b List.mem_cons_self
    refine ⟨min η (b - c), lt_min hη (by linarith), fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · linarith [min_le_right η (a - c)]
    · linarith [min_le_left η (b - c), hl a ha]

/-- Every platform trigger time lies at or after `now`. -/
lemma now_le_of_criticalAt {e : Execution n} {i : ℕ} (hR : Rel hk hkn hw hO₀ hi₀ π σ e i)
    {q : Fin n} {t : ℝ} (ht : CriticalAt k w e σ q t) : (snapAt I i).now ≤ t :=
  not_lt.1 fun hlt => hR.quiet q t ht.1 hlt ht

/-- In the window `[now, next arrival)`, the platform's trigger is ours. -/
lemma criticalAt_iff_window (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) (hst : (snapAt I i).stage = .idle) {t : ℝ}
    (h1 : (snapAt I i).now ≤ t) (h2 : ∀ a ∈ (snapAt I i).upcoming, t < a) (q : Fin n) :
    CriticalAt k w e σ q t ↔
      PagingWithDelay.PMD.TriggerCond I (snapAt I i).x (snapAt I i).pending (snapAt I i).claims t q := by
  have hx : StateValid k e.current.x := by
    rw [hR.x, PagingWithDelay.PMD.x_eq_baseState (I).valid (by intro e b; rw [hst]; simp),
      ← isRest_iff' hk hkn hw hO₀ hi₀ π]
    exact PagingWithDelay.PMD.baseState_isRest (I).valid i
  rw [criticalAt_iff hk hkn hw hO₀ hi₀ π hσ (hR.pend t h1 h2) hx, hR.x, hR.claims]
  exact ⟨fun h => h.2, fun h => ⟨hR.time.trans h1, h⟩⟩

/-- Upcoming arrivals lie strictly after `now` at a related index. -/
lemma now_lt_upcoming' {e : Execution n} {i : ℕ} (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) :
    ∀ a ∈ (snapAt I i).upcoming, (snapAt I i).now < a := by
  intro a ha
  by_cases hi : i ≤ (log I).length
  · exact PagingWithDelay.PMD.now_lt_upcoming (I).valid hi hR.pos ha
  · rw [PagingWithDelay.PMD.snapAt_of_ge_len (by omega),
      (PagingWithDelay.PMD.final_spec (I).valid).1] at ha
    simp at ha

/-- No platform trigger before `now`.

Proof sketch: `CriticalAt` needs `e.current.time ≤ t`, and `Rel.quiet` excludes
`t ∈ [e.current.time, now)`; so `{t | CriticalAt q t} ⊆ [now, ∞)` and its `sInf ≥ now`
(`le_csInf`). -/
lemma nextPageTime_ge (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) {q : Fin n} {t : ℝ}
    (ht : nextPageTime k w e σ q = some t) : (snapAt I i).now ≤ t := by
  unfold nextPageTime at ht
  split_ifs at ht with hne
  rw [← Option.some.inj ht]
  exact le_csInf hne fun t ht => now_le_of_criticalAt hk hkn hw hO₀ hi₀ π hR ht

/-- **A page triggers now for the platform iff it is critical now for us.**

Proof sketch: `S_q = {t | CriticalAt q t} ⊆ [now, ∞)` (`Rel.quiet`). For `t ∈ [now, a)`
(`a` the next arrival, `∞` if none) `Rel.pend` and `criticalAt_iff` (with
`StateValid k e.current.x` from `Rel.x`, idle `x = baseState`, `baseState_isRest`, `isRest_iff'`)
give `t ∈ S_q ↔ TriggerCond J x pending claims t q`. Then `sInf S_q = now` iff `TriggerCond`
holds at points of `[now, now + ε)` for all small `ε > 0`, which is `Critical` (for `ε ≤ a - now`). -/
lemma nextPageTime_eq_now_iff (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) (hst : (snapAt I i).stage = .idle) (q : Fin n) :
    nextPageTime k w e σ q = some (snapAt I i).now ↔
      Critical I (snapAt I i).x (snapAt I i).pending (snapAt I i).claims (snapAt I i).now q := by
  obtain ⟨η, hη, hgap⟩ := exists_gap _ _ (now_lt_upcoming' hk hkn hw hO₀ hi₀ π hR)
  have hwin : ∀ t, (snapAt I i).now ≤ t → t < (snapAt I i).now + η →
      (CriticalAt k w e σ q t ↔ PagingWithDelay.PMD.TriggerCond I (snapAt I i).x (snapAt I i).pending
        (snapAt I i).claims t q) := fun t h1 h2 =>
    criticalAt_iff_window hk hkn hw hO₀ hi₀ π hσ hR hst h1
      (fun a ha => lt_of_lt_of_le h2 (hgap a ha)) q
  have hlb := fun t (ht : t ∈ {t | CriticalAt k w e σ q t}) =>
    now_le_of_criticalAt hk hkn hw hO₀ hi₀ π hR ht
  have hbdd : BddBelow {t | CriticalAt k w e σ q t} := ⟨_, hlb⟩
  unfold nextPageTime
  constructor
  · intro h ε hε
    split_ifs at h with hne
    have h := Option.some.inj h
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne
      (show sInf _ < sInf {t | CriticalAt k w e σ q t} + min ε η by
        linarith [lt_min hε hη])
    rw [h] at htlt
    have h1 := hlb t ht
    exact ⟨t, h1, by linarith [min_le_left ε η],
      (hwin t h1 (by linarith [min_le_right ε η])).1 ht⟩
  · intro hc
    have hmem : ∀ ε > 0, ∃ τ ∈ {t | CriticalAt k w e σ q t}, τ < (snapAt I i).now + ε := by
      intro ε hε
      obtain ⟨τ, h1, h2, h3⟩ := hc (min ε η) (lt_min hε hη)
      exact ⟨τ, (hwin τ h1 (by linarith [min_le_right ε η])).2 h3,
        by linarith [min_le_left ε η]⟩
    obtain ⟨τ, hτ, -⟩ := hmem 1 one_pos
    rw [if_pos ⟨τ, hτ⟩]
    refine congrArg some (le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
      (le_csInf ⟨τ, hτ⟩ hlb))
    obtain ⟨τ', hτ', hlt⟩ := hmem ε hε
    exact lt_of_le_of_lt (csInf_le hbdd hτ') hlt

/-- **At the end of our log, the platform has no next event.**

Proof sketch: `final_spec`: `upcoming = []`, idle, `triggerTimes = ∅`. For `t < now`,
`Rel.quiet`; for `t ≥ now`, `Rel.pend` (no upcoming arrival) and `criticalAt_iff` would put `t`
in `triggerTimes`. So `{t | CriticalAt q t} = ∅`. -/
lemma nextPageTime_eq_none (hσ : ValidInstance σ) {e : Execution n}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e (log I).length) (q : Fin n) :
    nextPageTime k w e σ q = none := by
  obtain ⟨hup, -, hst, hT⟩ := PagingWithDelay.PMD.final_spec (I).valid
  unfold nextPageTime
  rw [if_neg]
  rintro ⟨t, ht⟩
  have h1 := now_le_of_criticalAt hk hkn hw hO₀ hi₀ π hR ht
  have h2 := (criticalAt_iff_window hk hkn hw hO₀ hi₀ π hσ hR hst h1 (by simp [hup]) q).1 ht
  have : t ∈ triggerTimes I (snapAt I (log I).length) := ⟨h1, q, h2⟩
  rw [hT] at this
  exact this

/-- If our log is empty, there are no requests and the platform has no event at all.

Proof sketch: `requests_eq_nil_of_log` and `J_requests` give `σ = []`; then `pending = []`, every
overshoot is `max 0 (0 - c - w) = 0` (claims `0`), so `CriticalAt` never holds. -/
lemma nextEvent_start_of_log_nil (hσ : ValidInstance σ) (hl : log I = []) :
    nextEvent k w π (start k O₀ i₀) σ = none := by
  have hreq := Sim.requests_eq_nil_of_log hl
  rw [J_requests, List.map_eq_nil_iff] at hreq
  subst hreq
  refine nextEvent_eq_none_of fun q => ?_
  unfold nextPageTime
  rw [if_neg]
  rintro ⟨t, -, ht, -⟩
  have hwq := Bridge.weight_pos_of_PMDWeights hw q
  simp [PagingDelay.PMD.overshoot, PagingDelay.PMD.pending, PagingDelay.PMD.pageDelay, start] at ht
  linarith

lemma nextEvent_of_final (hσ : ValidInstance σ) {e : Execution n}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e (log I).length) : nextEvent k w π e σ = none :=
  nextEvent_eq_none_of (nextPageTime_eq_none hk hkn hw hO₀ hi₀ π hσ hR)

/-- **The platform's next event is our critical service.** -/
lemma nextEvent_of_critical (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) (h : i < (log I).length) {p : Fin n}
    (hm : moveAt i h = .critical p) :
    nextEvent k w π e σ = some ((snapAt I i).now, p) := by
  obtain ⟨hst, htp, -⟩ := PagingWithDelay.PMD.critical_spec (I).valid h hm
  have hcrit := PagingWithDelay.PMD.triggerPage_spec htp
  apply nextEvent_eq_some_of_min
  · exact (nextPageTime_eq_now_iff hk hkn hw hO₀ hi₀ π hσ hR hst p).2 hcrit
  · intro q t hq
    rcases eq_or_lt_of_le (nextPageTime_ge hk hkn hw hO₀ hi₀ π hσ hR hq) with heq | hlt
    · right
      refine ⟨heq, ?_⟩
      rw [← heq] at hq
      have hq' := (nextPageTime_eq_now_iff hk hkn hw hO₀ hi₀ π hσ hR hst q).1 hq
      have := PagingWithDelay.PMD.triggerPage_tieRank_le htp hq'
      rw [J_tieRank, J_tieRank] at this
      exact Fin.le_def.2 this
    · exact Or.inl hlt

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Critical` -/
section

/-!
# Simulation bridge: the critical service

The platform's `criticalService` at our critical entry `i` (time `now`, page `p`) is our critical
move: same state (`pathEnd = criticalState`), claims (`θ` = our `claimFraction` at a critical
time), budgets (`bandLength = levelLen` deposits), and the requests on `p` are served.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage serviceEnd criticalState)

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

/-- **The critical service.** After the platform's `criticalService` at time `now` on `p`, the
relation holds at `i + 1` with equal times, and the recorded move is our entry's.

Proof sketch (`critical_spec`, `critical_facts`; `t = now`, `x = e.current.x` a rest state):
* `x`: `pathEnd_eq'`.
* claims: `overshoot_eq` (with `Rel.pend` at `t = now`, `Started` since `i ≥ 1`); the platform's
  `θ = (len/L)/denom` (`0` if `denom = 0`) equals `claimFraction = min 1 (len/L/denom)` because
  `Triggered` gives `len / L ≤ denom` (`pathLength_eq'`, `J_L`); `w q ≤ w p ↔ q ∈ lighter p`.
* budgets: `deposit_eq` for `j ≤ maxLevel`; above, `bandLength ≥ 0` (`le_max_left`).
* `moves_budget`: the new snapshot's budgets: `j ≤ maxLevel` are ours (`budget_nonneg`), the
  others `≥ 0` as above.
* `Chain` (`chain_push`), `moves_time` (`t = now ≥ e.current.time`), `time`, `quiet` (empty).
* `pend`: `pending_push` (time `now`): a request of the platform's pending list is filtered iff
  its page is at `δ` after the service, iff its page is `p` (`criticalState` has `x_p = δ`; a page
  `q ≠ p` with a pending request has `x_q > δ` before, `delta_lt_of_pending`, and does not
  decrease, `le_criticalState`); this is our filter `page ≠ p` (`List.Perm.filter`,
  `List.filter_map`). Future times: `pending_eq_of_no_arrival`.
* moves: `push_moves`, `tail_succ`, `entryMoves` of `.critical p`. -/
lemma rel_critical (hσ : ValidInstance σ) {e : Execution n} {i : ℕ}
    (hR : Rel hk hkn hw hO₀ hi₀ π σ e i) (h : i < (log I).length) {p : Fin n}
    (hm : moveAt i h = .critical p) :
    Rel hk hkn hw hO₀ hi₀ π σ (criticalService k w σ e (snapAt I i).now p) (i + 1) ∧
      (criticalService k w σ e (snapAt I i).now p).current.time = (snapAt I (i + 1)).now ∧
      (criticalService k w σ e (snapAt I i).now p).moves.map view ++ tail I (i + 1) =
        e.moves.map view ++ tail I i := by
  have hv := (I).valid
  obtain ⟨-, -, hs'⟩ := PagingWithDelay.PMD.critical_spec hv h hm
  obtain ⟨htrig, -, hrest, hδp, -⟩ := PagingWithDelay.PMD.critical_facts hv h hm
  have hxv : StateValid k e.current.x := by
    rw [hR.x]; exact (isRest_iff' hk hkn hw hO₀ hi₀ π _).1 hrest
  have hlen : pathLength k w e.current.x p = serviceEnd I (snapAt I i).x p := by
    rw [pathLength_eq' hk hkn hw hO₀ hi₀ π hxv, hR.x]
  have hend : pathEnd k w e.current.x p = criticalState I (snapAt I i).x p := by
    rw [pathEnd_eq' hk hkn hw hO₀ hi₀ π hxv, hR.x]
  have hP := hR.pend _ le_rfl (PagingWithDelay.PMD.started_of_pos hv h.le hR.pos)
  -- the claim fraction
  have hD : ∑ q ∈ Finset.univ.filter (fun q => w q ≤ w p),
      PagingDelay.PMD.overshoot k w e σ (snapAt I i).now q =
      ∑ q ∈ PagingWithDelay.PMD.lighter I p, PagingWithDelay.PMD.overshoot I (snapAt I i).pending
        (snapAt I i).claims q (snapAt I i).now := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [overshoot_eq hk hkn hw hO₀ hi₀ π hσ hP, hR.claims]
  have hθ : (if (∑ q ∈ PagingWithDelay.PMD.lighter I p, PagingWithDelay.PMD.overshoot I
      (snapAt I i).pending (snapAt I i).claims q (snapAt I i).now) = 0 then 0 else
      serviceEnd I (snapAt I i).x p / logFactor k / ∑ q ∈ PagingWithDelay.PMD.lighter I p,
        PagingWithDelay.PMD.overshoot I (snapAt I i).pending (snapAt I i).claims q
          (snapAt I i).now) =
      PagingWithDelay.PMD.claimFraction I (snapAt I i).x (snapAt I i).pending
        (snapAt I i).claims (snapAt I i).now p := by
    unfold PagingWithDelay.PMD.claimFraction
    have hD0 : 0 ≤ ∑ q ∈ PagingWithDelay.PMD.lighter I p, PagingWithDelay.PMD.overshoot I
        (snapAt I i).pending (snapAt I i).claims q (snapAt I i).now :=
      Finset.sum_nonneg fun q _ => le_max_left _ _
    split_ifs with h0
    · rw [h0, div_zero, min_eq_right zero_le_one]
    · rw [min_eq_right (div_le_one_of_le₀ htrig.2 hD0)]; rfl
  have hbud : ∀ j : ℕ, 0 ≤ e.current.budget j := fun j => by
    rcases le_or_gt (j : ℤ) (PagingWithDelay.PMD.maxLevel I) with hj | hj
    · rw [hR.budget j hj]; exact PagingWithDelay.PMD.budget_nonneg hv _ _
    · exact hR.budget_hi j hj
  have hnew : ∀ j : ℕ, 0 ≤ e.current.budget j + (if w p ≤ level j then
      bandLength k (pathLength k w e.current.x p) (level j) else 0) := fun j =>
    add_nonneg (hbud j) (by split_ifs <;> simp [bandLength])
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hs']; exact hend
  · have hθ' := hθ
    rw [← hD, ← hlen] at hθ'
    rw [hs']
    simp only [criticalService, push_current]
    rw [hθ']
    funext q
    simp only [Function.update_apply, PagingWithDelay.PMD.claimUpdate,
      PagingWithDelay.PMD.mem_lighter, hR.claims, overshoot_eq hk hkn hw hO₀ hi₀ π hσ hP,
      J_weight hk hkn hw hO₀ hi₀ π]
    split_ifs <;> simp
  · intro j hj
    rw [hs']
    simp only [criticalService, push_current]
    rw [deposit_eq hk hkn hw hO₀ hi₀ π _ _ _ j hj, hR.budget j hj, hlen]
  · intro j hj
    exact (hnew j).trans_eq rfl
  · intro m hm'
    simp only [criticalService, push_moves, List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | rfl
    · exact hR.moves_budget m hm'
    · exact hnew
  · exact chain_push hR.chain _ _
  · intro m hm'
    simp only [criticalService, push_moves, List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | rfl
    · exact (hR.moves_time m hm').trans hR.time
    · exact le_rfl
  · rw [hs']; exact le_rfl
  · intro q t h1 h2
    rw [hs'] at h2
    exact absurd h2 (not_lt.2 h1)
  · intro t ht hup
    rw [hs'] at ht hup ⊢
    dsimp only at ht hup ⊢
    have hno : ∀ r ∈ σ, ¬ ((snapAt I i).now < r.arrival ∧ r.arrival ≤ t) := by
      rintro r hr ⟨h1, h2⟩
      have hr' : Thm1.conv r ∈ (I).requests := List.mem_map_of_mem hr
      rcases arrival_le_now_or_mem_upcoming hr' i with h3 | h3
      · rw [Thm1.conv_arrival] at h3; linarith
      · have := hup _ h3; rw [Thm1.conv_arrival] at this; linarith
    rw [pending_eq_of_no_arrival k σ _ hno ht]
    simp only [criticalService]
    rw [pending_push k σ le_rfl]
    have hmf : ((pending k e σ (snapAt I i).now).filter
        fun r => decide (pathEnd k w e.current.x p r.page ≠ delta k)).map Thm1.conv =
        ((pending k e σ (snapAt I i).now).map Thm1.conv).filter
          (fun ρ => decide (criticalState I (snapAt I i).x p ρ.page ≠ (I).delta)) := by
      rw [List.filter_map, hend]
      congr 1
      exact List.filter_congr fun r _ => by simp [J_delta]
    refine (List.Perm.of_eq hmf).trans ((hP.filter _).trans
      (List.Perm.of_eq (List.filter_congr fun ρ hρ => ?_)))
    have hρδ := PagingWithDelay.PMD.delta_lt_of_pending hv hρ
    by_cases hq : ρ.page = p
    · subst hq
      simp [PagingWithDelay.PMD.criticalState_self hv hrest hδp, J_delta]
    · have := PagingWithDelay.PMD.le_criticalState hv hrest hδp hq
      have : criticalState I (snapAt I i).x p ρ.page ≠ delta k := by
        rw [← J_delta hk hkn hw hO₀ hi₀ π]; exact (hρδ.trans_le this).ne'
      simp [hq, J_delta, this]
  · rw [hs']; rfl
  · rw [tail_succ h, hm]
    simp only [criticalService, push_moves, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append, entryMoves, view]
    rw [← hR.x, hend, hR.x]

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge.Level` -/
section

/-!
# Simulation bridge: the level pass

After a critical service, the platform folds `preemptiveService` over `levels w = [0, …, maxLevel]`
and we examine the levels `minLevel = 0, …, maxLevel`. Level by level:

* the conditions agree (`precond_iff`); a failed condition is our `skip` (no platform move);
* the hole is ours (`rel_openHole`); the platform fixes the list `E = tripList` of pages to visit,
  which is our order of round-trip candidates (`TripList`, `tripList_open`): we re-pick the
  candidate after each trip, but only the visited page's requests leave, so the order of the
  others is unchanged (`tripList_tail`);
* a round trip is ours (`rel_trip`), and the hole is closed in the same way (`rel_close`).

Inside a level pass all times equal `now` (`RelEq`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage maxLevel minLevel levelWeight
  preemptCondition tripCandidate pageDeadline afterLevel hole)

/-! ### Round-trip lists -/

/-- `E` lists the pages of level `≤ j` with a request in `P`, strictly increasing in
(deadline at `t`, tie rank): the order in which our loop makes its round trips. -/
def TripList {n : ℕ} (input : PagingWithDelay.Instance (Fin n))
    (P : List (PagingWithDelay.Request (Fin n))) (t : ℝ) (j : ℤ) (E : List (Fin n)) : Prop :=
  (∀ q, q ∈ E ↔ PagingWithDelay.PMD.level input q ≤ j ∧ ∃ ρ ∈ P, ρ.page = q) ∧
    E.Pairwise fun p q =>
      toLex (pageDeadline input P t p, input.tieRank p) <
        toLex (pageDeadline input P t q, input.tieRank q)

section TripList

variable {n : ℕ} {input : PagingWithDelay.Instance (Fin n)}
  {P : List (PagingWithDelay.Request (Fin n))} {t : ℝ} {j : ℤ}

/-- No candidate iff nothing is left to visit. Proof: `tripCandidate` is an `argmin` over the
pending requests of level `≤ j` (`List.argmin_eq_none`, `tripCandidate_ne_none`). -/
lemma tripCandidate_eq_none_iff {E : List (Fin n)} (hE : TripList input P t j E) :
    tripCandidate input P t j = none ↔ E = [] := by
  constructor
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro q hq
    obtain ⟨hl, ρ, hρ, rfl⟩ := (hE.1 q).1 hq
    exact PagingWithDelay.PMD.ExcessProof.tripCandidate_ne_none hρ hl h
  · rintro rfl
    unfold tripCandidate
    rw [List.argmin_eq_none, List.eq_nil_iff_forall_not_mem]
    intro ρ hρ
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    simpa using (hE.1 ρ.page).2 ⟨hρ.2, ρ, hρ.1, rfl⟩

/-- The candidate's page is the head of the list. Proof: the candidate's page is in `E`; the
head `h` of `E` has a request of level `≤ j`, so by `tripCandidate_lex` the candidate's key is
`≤` that of `h`, while `Pairwise` makes every other element's key `>` that of `h`. -/
lemma tripList_head {E : List (Fin n)} (hE : TripList input P t j E)
    {ρ : PagingWithDelay.Request (Fin n)} (h : tripCandidate input P t j = some ρ) :
    ∃ rest, E = ρ.page :: rest := by
  obtain ⟨hm, hl, hlex⟩ := PagingWithDelay.PMD.ExcessProof.tripCandidate_lex h
  have hmem : ρ.page ∈ E := (hE.1 _).2 ⟨hl, ρ, hm, rfl⟩
  match E, hE, hmem with
  | a :: rest, hE, hmem =>
    refine ⟨rest, ?_⟩
    rcases List.mem_cons.1 hmem with h1 | h1
    · rw [h1]
    · obtain ⟨hla, ρ', hρ', rfl⟩ := (hE.1 a).1 (by simp)
      exact absurd (List.rel_of_pairwise_cons hE.2 h1)
        (not_lt.2 (Prod.Lex.toLex_le_toLex.2 (hlex ρ' hρ' hla)))

/-- After the round trip on the head `q`, the rest of the list is the round-trip list of the
remaining requests. Proof: the deadlines of pages `≠ q` do not change (`pageDelay_filter_ne`),
and `q ∉ rest` (strict `Pairwise`). -/
lemma tripList_tail {q : Fin n} {E : List (Fin n)} (hE : TripList input P t j (q :: E)) :
    TripList input (P.filter fun ρ => decide (ρ.page ≠ q)) t j E := by
  have hdl : ∀ p, p ≠ q →
      pageDeadline input (P.filter fun ρ => decide (ρ.page ≠ q)) t p = pageDeadline input P t p := by
    intro p hp
    unfold pageDeadline
    simp_rw [PagingWithDelay.PMD.pageDelay_filter_ne P hp]
  have hne : ∀ p ∈ E, p ≠ q := fun p hp h =>
    lt_irrefl _ (List.rel_of_pairwise_cons hE.2 (h ▸ hp))
  refine ⟨fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  · obtain ⟨hl, ρ, hρ, rfl⟩ := (hE.1 _).1 (List.mem_cons_of_mem _ hp)
    exact ⟨hl, ρ, List.mem_filter.2 ⟨hρ, by simpa using hne _ hp⟩, rfl⟩
  · rintro ⟨hl, ρ, hρ, rfl⟩
    rw [List.mem_filter] at hρ
    rcases List.mem_cons.1 ((hE.1 ρ.page).2 ⟨hl, ρ, hρ.1, rfl⟩) with h | h
    · simp [h] at hρ
    · exact h
  · refine List.Pairwise.imp_of_mem (fun ha hb hab => ?_) (List.pairwise_cons.1 hE.2).2
    rw [hdl _ (hne _ ha), hdl _ (hne _ hb)]
    exact hab

end TripList

/-! ### Generic helpers -/

/-- Option deadlines with `none = ∞`. -/
def wt : Option ℝ → WithTop ℝ
  | none => ⊤
  | some x => (x : WithTop ℝ)

lemma deadlineLE_iff (a b : Option ℝ) : deadlineLE a b ↔ wt a ≤ wt b := by
  cases a <;> cases b <;> simp [deadlineLE, wt]

lemma wt_inj {a b : Option ℝ} : wt a = wt b ↔ a = b := by
  cases a <;> cases b <;> simp [wt]

/-- The comparator of `tripList` is lexicographic on `(deadline, π)`. -/
lemma cmp_iff {n : ℕ} (π : Fin n ≃ Fin n) (a b : Option ℝ) (p q : Fin n) :
    (deadlineLE a b ∧ (a ≠ b ∨ π p ≤ π q)) ↔ toLex (wt a, π p) ≤ toLex (wt b, π q) := by
  rw [Prod.Lex.toLex_le_toLex, deadlineLE_iff, ne_eq, ← wt_inj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl (lt_of_le_of_ne h1 h2)
    · rcases h1.lt_or_eq with h | h
      exacts [Or.inl h, Or.inr ⟨h, h2⟩]
  · rintro (h | ⟨h, h'⟩)
    exacts [⟨h.le, Or.inl h.ne⟩, ⟨h.le, Or.inr h'⟩]

lemma pending_push' {n k : ℕ} {σ : Instance n} {e : Execution n} {s : Snapshot n}
    {kind : MoveKind n} {t₀ t : ℝ} (hs : s.time = t₀) (h1 : t₀ ≤ t)
    (hna : ∀ r ∈ σ, ¬ (t₀ < r.arrival ∧ r.arrival ≤ t)) :
    pending k (push e s kind) σ t =
      (pending k e σ t).filter (fun r => decide (s.x r.page ≠ delta k)) := by
  rw [pending_eq_of_no_arrival k σ _ hna h1, pending_eq_of_no_arrival k σ e hna h1]
  exact pending_push k σ hs.ge

lemma filter_self_of {n : ℕ} {L : List (Request n)} {P : List (PagingWithDelay.Request (Fin n))}
    (hP : (L.map Thm1.conv).Perm P) {x : Fin n → ℝ} {d : ℝ} (hx : ∀ ρ ∈ P, d < x ρ.page) :
    L.filter (fun r => decide (x r.page ≠ d)) = L :=
  List.filter_eq_self.2 fun r hr => by
    have := hx _ (hP.subset (List.mem_map_of_mem hr))
    rw [Thm1.conv_page] at this
    simpa using this.ne'

lemma update_budget_eq {B : ℕ → ℝ} {B' : ℤ → ℝ} {j i : ℕ} {u u' : ℝ} (hB : B i = B' i)
    (hu : u = u') : Function.update B j u i = Function.update B' (j : ℤ) u' (i : ℤ) := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hu]
  · rw [Function.update_of_ne hij, Function.update_of_ne (by exact_mod_cast hij), hB]

lemma push_moves_mem {n : ℕ} {e : Execution n} {s : Snapshot n} {kind : MoveKind n} {m : Move n}
    (hm : m ∈ (push e s kind).moves) :
    m ∈ e.moves ∨ (m.after.time = s.time ∧ m.after.budget = s.budget) := by
  rw [push_moves, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  exacts [Or.inl hm, Or.inr ⟨rfl, rfl⟩]

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

variable (σ) in
/-- The relation inside a block of moves at one instant. -/
def RelEq (e : Execution n) (l : ℕ) : Prop :=
  Rel hk hkn hw hO₀ hi₀ π σ e l ∧ e.current.time = (snapAt I l).now

lemma no_arrival {l : ℕ} {t : ℝ} (h2 : ∀ a ∈ (snapAt I l).upcoming, t < a) :
    ∀ r ∈ σ, ¬ ((snapAt I l).now < r.arrival ∧ r.arrival ≤ t) := by
  rintro r hr ⟨h3, h4⟩
  have hc : Thm1.conv r ∈ (I).requests := List.mem_map_of_mem hr
  rcases arrival_le_now_or_mem_upcoming hc l with h | h <;> rw [Thm1.conv_arrival] at h
  · linarith
  · linarith [h2 _ h]

lemma level_le_max {l : ℕ} {j : ℤ} {b : Fin n → ℝ}
    (h : (snapAt I l).stage = .examine j ∨ (snapAt I l).stage = .preempt j b) :
    j ≤ maxLevel I := by
  have := PagingWithDelay.PMD.stageOK (I).valid l
  rcases h with h | h <;> rw [h] at this <;> exact this.2

/-- Building the relation after a block of moves at time `now`. -/
lemma relEq_of {e e' : Execution n} {l : ℕ} (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l)
    (hnow : (snapAt I (l + 1)).now = (snapAt I l).now)
    (hup : (snapAt I (l + 1)).upcoming = (snapAt I l).upcoming)
    (htime : e'.current.time = e.current.time)
    (hx : e'.current.x = (snapAt I (l + 1)).x)
    (hcl : e'.current.claims = (snapAt I (l + 1)).claims)
    (hb : ∀ j : ℕ, (j : ℤ) ≤ maxLevel I → e'.current.budget j = (snapAt I (l + 1)).budget j)
    (hbhi : ∀ j : ℕ, maxLevel I < j → 0 ≤ e'.current.budget j)
    (hchain : Chain e')
    (hmoves : ∀ m ∈ e'.moves, m ∈ e.moves ∨
      (m.after.time = e.current.time ∧ m.after.budget = e'.current.budget))
    (hpend : ∀ t, (snapAt I l).now ≤ t → (∀ a ∈ (snapAt I l).upcoming, t < a) →
      ((pending k e' σ t).map Thm1.conv).Perm (snapAt I (l + 1)).pending) :
    RelEq hk hkn hw hO₀ hi₀ π σ e' (l + 1) := by
  obtain ⟨hR, ht⟩ := hR
  have hnn : ∀ j : ℕ, 0 ≤ e'.current.budget j := by
    intro j
    by_cases hj : (j : ℤ) ≤ maxLevel I
    · rw [hb j hj]; exact PagingWithDelay.PMD.budget_nonneg (I).valid _ _
    · exact hbhi j (not_le.1 hj)
  have hte : e'.current.time = (snapAt I (l + 1)).now := by rw [htime, ht, hnow]
  refine ⟨⟨by omega, hx, hcl, hb, hbhi, fun m hm j => ?_, hchain, fun m hm => ?_, hte.le,
    fun p t h1 h2 => absurd (h1.trans_lt h2) (by rw [hte]; exact lt_irrefl _), fun t h1 h2 => ?_⟩,
    hte⟩
  · rcases hmoves m hm with hm | ⟨-, hb'⟩
    · exact hR.moves_budget m hm j
    · rw [hb']; exact hnn j
  · rcases hmoves m hm with hm | ⟨ht', -⟩
    · rw [htime]; exact hR.moves_time m hm
    · rw [htime, ht']
  · rw [hnow] at h1; rw [hup] at h2; exact hpend t h1 h2

/-- **The conditions of a preemptive service agree** (`Rel.budget`, `levelWeight_natCast`,
`mass_eq`, `J_delta`). -/
lemma precond_iff {e : Execution n} {l : ℕ} (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) {j : ℕ}
    (hj : (j : ℤ) ≤ maxLevel I) :
    precond k w j e ↔ preemptCondition I (snapAt I l).x (snapAt I l).budget j := by
  unfold precond preemptCondition
  rw [hR.1.budget j hj, mass_eq hk hkn hw hO₀ hi₀ π (σ := σ), hR.1.x, ← levelWeight_natCast]
  exact Iff.rfl

/-- A skip changes only the stage (`skip_spec`). -/
lemma rel_skip {e : Execution n} {l : ℕ} (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l)
    (h : l < (log I).length) {j : ℤ} (hm : moveAt l h = .skip j) :
    RelEq hk hkn hw hO₀ hi₀ π σ e (l + 1) := by
  obtain ⟨-, -, hs⟩ := PagingWithDelay.PMD.skip_spec (I).valid h hm
  exact relEq_of hk hkn hw hO₀ hi₀ π hR (by rw [hs]) (by rw [hs]) rfl (by rw [hs]; exact hR.1.x)
    (by rw [hs]; exact hR.1.claims) (fun i hi => by rw [hs]; exact hR.1.budget i hi)
    hR.1.budget_hi hR.1.chain (fun m hm => Or.inl hm)
    (fun t h1 h2 => by rw [hs]; exact hR.1.pend t h1 h2)

/-- **Opening the hole.**

Proof sketch (`openHole_spec`): `x`: `openSnap_x` (the condition holds by `precond_iff`); budget
of level `j`: `W (1 - δ) = holePayment` (`levelWeight_natCast`, `J_delta`), other levels and
claims unchanged; `moves_budget`: the new budgets are ours (`budget_nonneg`) or unchanged above
`maxLevel` (`j ≤ maxLevel` from `Run/Steps.stageOK`). `pend`: `pending_push`; no pending page is
at `δ` in the hole (`x_q > δ` for pending `q`, and the hole only increases `x`), so the filter is
trivial. Recorded move: `(openHole j, x, hole x j, now)`. -/
lemma rel_openHole (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {j : ℕ}
    (hm : moveAt l h = .openHole j) :
    RelEq hk hkn hw hO₀ hi₀ π σ (push e (openSnap k w j e) (.openHole j)) (l + 1) ∧
      (push e (openSnap k w j e) (.openHole j)).moves.map view ++ tail I (l + 1) =
        e.moves.map view ++ tail I l := by
  obtain ⟨hst, hpc, hs⟩ := PagingWithDelay.PMD.openHole_spec (I).valid h hm
  have hj : (j : ℤ) ≤ maxLevel I := level_le_max hk hkn hw hO₀ hi₀ π (b := fun _ => 0) (Or.inl hst)
  have hmass := ((precond_iff hk hkn hw hO₀ hi₀ π hR hj).2 hpc).2
  have ht := hR.2
  have hx : (openSnap k w j e).x = (snapAt I (l + 1)).x := by
    rw [hs, openSnap_x hk hkn hw hO₀ hi₀ π (σ := σ) hmass, hR.1.x]
  have hbj : ∀ i : ℕ, maxLevel I < i → (openSnap k w j e).budget i = e.current.budget i :=
    fun i hi => Function.update_of_ne (by rintro rfl; omega) _ _
  refine ⟨relEq_of hk hkn hw hO₀ hi₀ π hR (by rw [hs]) (by rw [hs]) rfl hx
    (by rw [hs]; exact hR.1.claims) (fun i hi => ?_)
    (fun i hi => by rw [push_current, hbj i hi]; exact hR.1.budget_hi i hi)
    (chain_push hR.1.chain _ _) (fun m hm => push_moves_mem hm) (fun t h1 h2 => ?_), ?_⟩
  · rw [hs]
    refine update_budget_eq (hR.1.budget i hi) ?_
    rw [hR.1.budget j hj]
    unfold PagingWithDelay.PMD.holePayment
    rw [levelWeight_natCast]
    rfl
  · rw [pending_push' (s := openSnap k w j e) ht h1 (no_arrival hk hkn hw hO₀ hi₀ π h2), hs]
    have hP := hR.1.pend t h1 h2
    rw [filter_self_of hP (d := delta k) (x := (openSnap k w j e).x) fun ρ hρ => ?_]
    · exact hP
    · rw [hx]
      exact PagingWithDelay.PMD.delta_lt_of_pending (I).valid (by rw [hs]; exact hρ)
  · have hv : view ⟨e.current, openSnap k w j e, .openHole j⟩ =
        (.openHole j, (snapAt I l).x, hole I (snapAt I l).x j, (snapAt I l).now) := by
      show (MoveKind.openHole j, e.current.x, (openSnap k w j e).x, e.current.time) = _
      rw [hx, hs, hR.1.x, ht]
    rw [tail_succ h, hm, push_moves, List.map_append, List.append_assoc, List.map_singleton, hv]
    simp [entryMoves]

/-- **The platform's round-trip list is ours.**

Proof sketch: `rs = pending k e σ now` and `(rs.map conv).Perm pending` (`Rel.pend`; pending is
unchanged by `openHole`, `openHole_spec`). Membership: `List.mem_mergeSort`, `List.mem_filter`,
`Finset.mem_toList`, `pageLevel_le_iff`, `Thm1.conv_page`. Order: the comparator of `tripList` is
total and transitive (lexicographic on `(effectiveDeadline, π)`, with `none = ∞`), so the merge
sort is sorted (`List.sorted_mergeSort`); by `effectiveDeadline_eq` the deadlines are `some` of
our `pageDeadline`; the list has no duplicates (`Finset.nodup_toList`, `List.Perm.nodup`), and
`π` is injective, so the order is strict lexicographic. -/
lemma tripList_open (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {j : ℕ}
    (hm : moveAt l h = .openHole j) :
    TripList I (snapAt I (l + 1)).pending (snapAt I (l + 1)).now j (tripList k w π σ j e) := by
  obtain ⟨-, -, hs⟩ := PagingWithDelay.PMD.openHole_spec (I).valid h hm
  have ht := hR.2
  have hnow : (snapAt I (l + 1)).now = (snapAt I l).now := by rw [hs]
  have hpend : (snapAt I (l + 1)).pending = (snapAt I l).pending := by rw [hs]
  rw [hnow, hpend, ← ht]
  have hP : ((pending k e σ e.current.time).map Thm1.conv).Perm (snapAt I l).pending := by
    rw [ht]
    exact hR.1.pend _ le_rfl fun a ha =>
      PagingWithDelay.PMD.now_lt_upcoming (I).valid h.le (by have := hR.1.pos; omega) ha
  have hmem : ∀ q, q ∈ tripList k w π σ j e ↔
      w q ≤ level j ∧ ∃ r ∈ pending k e σ e.current.time, r.page = q := by
    intro q
    simp [tripList, List.mem_mergeSort, List.mem_filter]
  refine ⟨fun q => ?_, ?_⟩
  · rw [hmem, pageLevel_le_iff hk hkn hw hO₀ hi₀ π]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Thm1.conv r, hP.subset (List.mem_map_of_mem hr), Thm1.conv_page r⟩
    · rintro ⟨ρ, hρ, rfl⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (hP.symm.subset hρ)
      exact ⟨r, hr, (Thm1.conv_page r).symm⟩
  · have hdl : ∀ q ∈ tripList k w π σ j e, effectiveDeadline w (pending k e σ e.current.time) q
        e.current.time = some (pageDeadline I (snapAt I l).pending e.current.time q) :=
      fun q hq => effectiveDeadline_eq hk hkn hw hO₀ hi₀ π (pending_valid hσ e _) hP
        ((hmem q).1 hq).2 _
    have hnd : (tripList k w π σ j e).Nodup :=
      (List.mergeSort_perm _ _).nodup_iff.2 ((Finset.nodup_toList _).filter _)
    revert hdl hnd
    unfold tripList
    intro hdl hnd
    refine List.Pairwise.imp_of_mem ?_ ((List.pairwise_mergeSort ?_ ?_ _).and hnd)
    · rintro p q hp hq ⟨h1, hne⟩
      simp only [decide_eq_true_eq] at h1
      rw [cmp_iff, hdl p hp, hdl q hq] at h1
      have hlt := lt_of_le_of_ne h1 fun h => hne (π.injective (Prod.ext_iff.1 (toLex.injective h)).2)
      rw [Prod.Lex.toLex_lt_toLex] at hlt ⊢
      simp only [wt, WithTop.coe_lt_coe, WithTop.coe_inj] at hlt
      rcases hlt with h | ⟨h, h'⟩
      exacts [Or.inl h, Or.inr ⟨h, h'⟩]
    · intro a b c h1 h2
      simp only [decide_eq_true_eq] at h1 h2 ⊢
      rw [cmp_iff] at h1 h2 ⊢
      exact h1.trans h2
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rw [cmp_iff, cmp_iff]
      exact le_total _ _

/-- **A round trip.**

Proof sketch (`trip_spec`): after visit and return, `x` is the hole state again, the claim of
`ρ.page` is `0`, the budget of level `j` drops by `w q (x_q - δ) = tripCost`. `pend`:
`pending_push` twice: the visit holds `ρ.page` at `δ` (serves exactly its pending requests: other
pending pages are `> δ`), the return holds the hole state (serves nothing). Recorded moves:
`(visit q, x, x[q ↦ δ], now)`, `(returnTrip q, x[q ↦ δ], x, now)`. -/
lemma rel_trip (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {j : ℕ}
    {ρ : PagingWithDelay.Request (Fin n)} (hm : moveAt l h = .trip j ρ) :
    RelEq hk hkn hw hO₀ hi₀ π σ (tripStep k w j ρ.page e) (l + 1) ∧
      (tripStep k w j ρ.page e).moves.map view ++ tail I (l + 1) = e.moves.map view ++ tail I l := by
  obtain ⟨⟨b, hst⟩, -, -, hs⟩ := PagingWithDelay.PMD.trip_spec (I).valid h hm
  have hj : (j : ℤ) ≤ maxLevel I := level_le_max hk hkn hw hO₀ hi₀ π (Or.inr hst)
  have ht := hR.2
  have hmv : (tripStep k w j ρ.page e).moves = e.moves ++
      [⟨e.current, visitSnap k w j ρ.page e, .visit ρ.page⟩,
        ⟨visitSnap k w j ρ.page e, { visitSnap k w j ρ.page e with x := e.current.x },
          .returnTrip ρ.page⟩] := by
    unfold tripStep
    rw [push_moves, push_moves, List.append_assoc]
    rfl
  refine ⟨relEq_of hk hkn hw hO₀ hi₀ π hR (by rw [hs]) (by rw [hs]) rfl
    (by rw [hs]; exact hR.1.x) (by rw [hs]; exact congrArg (Function.update · _ _) hR.1.claims)
    (fun i hi => ?_) (fun i hi => ?_) (chain_push (chain_push hR.1.chain _ _) _ _)
    (fun m hm => ?_) (fun t h1 h2 => ?_), ?_⟩
  · rw [hs]
    refine update_budget_eq (hR.1.budget i hi) ?_
    rw [hR.1.budget j hj, hR.1.x]
    rfl
  · show 0 ≤ Function.update e.current.budget j _ i
    rw [Function.update_of_ne (by rintro rfl; omega)]
    exact hR.1.budget_hi i hi
  · rw [hmv] at hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | rfl | rfl
    exacts [Or.inl hm, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩]
  · have hna := no_arrival hk hkn hw hO₀ hi₀ π h2
    have hP := hR.1.pend t h1 h2
    have hxl : ∀ r ∈ pending k e σ t, delta k < e.current.x r.page := fun r hr => by
      have := PagingWithDelay.PMD.delta_lt_of_pending (I).valid (hP.subset (List.mem_map_of_mem hr))
      rwa [Thm1.conv_page, ← hR.1.x] at this
    unfold tripStep
    rw [pending_push' (s := { visitSnap k w j ρ.page e with x := e.current.x }) ht h1 hna,
      pending_push' (s := visitSnap k w j ρ.page e) ht h1 hna, List.filter_filter, hs]
    rw [List.filter_congr (q := fun r => decide (r.page ≠ ρ.page)) fun r hr => ?_]
    · show (List.map Thm1.conv _).Perm
        ((snapAt I l).pending.filter fun ρ' => decide (ρ'.page ≠ ρ.page))
      have := hP.filter (fun ρ' => decide (ρ'.page ≠ ρ.page))
      rw [List.filter_map] at this
      simpa [Function.comp_def, Thm1.conv_page] using this
    · have hx := hxl r hr
      by_cases hq : r.page = ρ.page
      · simp [visitSnap, hq]
      · simp [visitSnap, hq, hx.ne']
  · rw [tail_succ h, hm, hmv]
    simp [view, entryMoves, visitSnap, hR.1.x, ht]
    rfl

/-- **Closing the hole** returns to the state `b` the hole was opened from.

Proof sketch (`closeHole_spec`): `x := b`; `pend`: `pending_push`, no pending page at `δ` in `b`
(`delta_lt_baseState_of_pending`). Recorded move: `(closeHole j, x, b, now)`. -/
lemma rel_close (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (h : l < (log I).length) {j : ℕ} {b : Fin n → ℝ}
    (hst : (snapAt I l).stage = .preempt j b) {stop : Option (PagingWithDelay.Request (Fin n))}
    (hm : moveAt l h = .closeHole j stop) :
    RelEq hk hkn hw hO₀ hi₀ π σ (push e { e.current with x := b } (.closeHole j)) (l + 1) ∧
      (push e { e.current with x := b } (.closeHole j)).moves.map view ++ tail I (l + 1) =
        e.moves.map view ++ tail I l := by
  obtain ⟨b', hst', -, hs⟩ := PagingWithDelay.PMD.closeHole_spec (I).valid h hm
  rw [hst] at hst'
  injection hst' with hj' hb
  subst hb
  have ht := hR.2
  refine ⟨relEq_of hk hkn hw hO₀ hi₀ π (e' := push e { e.current with x := b } (.closeHole j)) hR
    (by rw [hs]) (by rw [hs]) rfl (by rw [hs]; rfl)
    (by rw [hs]; exact hR.1.claims) (fun i hi => by rw [hs]; exact hR.1.budget i hi)
    hR.1.budget_hi (chain_push hR.1.chain _ _)
    (fun m hm => push_moves_mem (s := { e.current with x := b }) hm)
    (fun t h1 h2 => ?_), ?_⟩
  · rw [pending_push' (s := { e.current with x := b }) ht h1 (no_arrival hk hkn hw hO₀ hi₀ π h2),
      hs]
    have hP := hR.1.pend t h1 h2
    rw [filter_self_of hP (d := delta k) fun ρ hρ => ?_]
    · exact hP
    · have := PagingWithDelay.PMD.delta_lt_baseState_of_pending (I).valid hρ
      rwa [PagingWithDelay.PMD.baseState_of_preempt' hst] at this
  · rw [tail_succ h, hm, push_moves]
    simp [view, entryMoves, hst, hR.1.x, ht]

/-! ### Assembling a preemptive service and the level pass -/

/-- **The round trips** of a level-`j` preemptive service. -/
lemma rel_roundTrips (hσ : ValidInstance σ) {j : ℕ} (hj : (j : ℤ) ≤ maxLevel I)
    {b : Fin n → ℝ} :
    ∀ (E : List (Fin n)) (e : Execution n) (l : ℕ), RelEq hk hkn hw hO₀ hi₀ π σ e l →
      (snapAt I l).stage = .preempt j b →
      TripList I (snapAt I l).pending (snapAt I l).now j E →
      ∃ l', ∃ h' : l' < (log I).length, l ≤ l' ∧
        RelEq hk hkn hw hO₀ hi₀ π σ (roundTrips k w j E e) l' ∧
        (snapAt I l').stage = .preempt j b ∧ (∃ stop, moveAt l' h' = .closeHole j stop) ∧
        (roundTrips k w j E e).moves.map view ++ tail I l' = e.moves.map view ++ tail I l ∧
        critCount I l' = critCount I l
  | [], e, l, hR, hst, hE => by
    obtain ⟨h, hcase⟩ := preempt_step hst
    have hnone := (tripCandidate_eq_none_iff hE).2 rfl
    rcases hcase with ⟨-, hm⟩ | ⟨ρ, hρ, -⟩ | ⟨ρ, hρ, -⟩
    · exact ⟨l, h, le_rfl, hR, hst, ⟨none, hm⟩, rfl, rfl⟩
    · rw [hnone] at hρ; cases hρ
    · rw [hnone] at hρ; cases hρ
  | q :: qs, e, l, hR, hst, hE => by
    obtain ⟨h, hcase⟩ := preempt_step hst
    rcases hcase with ⟨hnone, -⟩ | ⟨ρ, hρ, hb, hm, hst'⟩ | ⟨ρ, hρ, hb, hm⟩
    · exact absurd ((tripCandidate_eq_none_iff hE).1 hnone) (List.cons_ne_nil _ _)
    · obtain ⟨rest, hrest⟩ := tripList_head hE hρ
      obtain ⟨rfl, rfl⟩ := List.cons.inj hrest
      have hbud : e.current.budget j ≥ level j := by
        rw [hR.1.budget j hj, ← levelWeight_natCast]; exact hb
      rw [roundTrips_cons_of hbud]
      obtain ⟨hR', heq⟩ := rel_trip hk hkn hw hO₀ hi₀ π hσ hR h hm
      have hE' : TripList I (snapAt I (l + 1)).pending (snapAt I (l + 1)).now j qs := by
        obtain ⟨-, -, -, hs⟩ := PagingWithDelay.PMD.trip_spec (I).valid h hm
        rw [hs]
        exact tripList_tail hE
      obtain ⟨l', h', hll', hR'', hst'', hclose, heq', hc'⟩ :=
        rel_roundTrips hσ hj qs _ (l + 1) hR' hst' hE'
      exact ⟨l', h', by omega, hR'', hst'', hclose, heq'.trans heq,
        hc'.trans (critCount_succ_of_not h (by rw [hm]; simp)).symm⟩
    · obtain ⟨rest, hrest⟩ := tripList_head hE hρ
      have hbud : ¬ e.current.budget j ≥ level j := by
        rw [hR.1.budget j hj, ← levelWeight_natCast]; exact not_le.2 hb
      rw [roundTrips_cons_of_not hbud]
      exact ⟨l, h, le_rfl, hR, hst, ⟨_, hm⟩, rfl, rfl⟩

lemma entryMoves_skip (s : Snap (Fin n)) (j : ℤ) : entryMoves I s (.skip j) = [] := rfl

/-- **One level** of the level pass: the platform's `preemptiveService j` is our examination of
level `j` (a skip, or a whole preemptive service). -/
lemma rel_level (hσ : ValidInstance σ) {j : ℕ} (hj : (j : ℤ) ≤ maxLevel I) {e : Execution n}
    {l : ℕ} (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (hst : (snapAt I l).stage = .examine j) :
    ∃ l', l < l' ∧ l' ≤ (log I).length ∧
      RelEq hk hkn hw hO₀ hi₀ π σ (preemptiveService k w π σ j e) l' ∧
      (snapAt I l').stage = afterLevel I j ∧
      (preemptiveService k w π σ j e).moves.map view ++ tail I l' = e.moves.map view ++ tail I l ∧
      critCount I l' = critCount I l := by
  obtain ⟨h, hm | hm⟩ := examine_step hst
  · obtain ⟨-, hnc, hs⟩ := PagingWithDelay.PMD.skip_spec (I).valid h hm
    have hpc : ¬ precond k w j e :=
      fun hc => hnc ((precond_iff hk hkn hw hO₀ hi₀ π hR hj).1 hc)
    rw [preemptiveService_of_not hpc]
    refine ⟨l + 1, by omega, h, rel_skip hk hkn hw hO₀ hi₀ π hR h hm, by rw [hs], ?_, ?_⟩
    · rw [tail_succ h, hm, entryMoves_skip, List.nil_append]
    · exact (critCount_succ_of_not h (by rw [hm]; simp)).symm
  · obtain ⟨-, hc, hs⟩ := PagingWithDelay.PMD.openHole_spec (I).valid h hm
    have hpc : precond k w j e := (precond_iff hk hkn hw hO₀ hi₀ π hR hj).2 hc
    rw [preemptiveService_of hpc]
    obtain ⟨hR1, heq1⟩ := rel_openHole hk hkn hw hO₀ hi₀ π hσ hR h hm
    have hst1 : (snapAt I (l + 1)).stage = .preempt j (snapAt I l).x := by rw [hs]
    have hE := tripList_open hk hkn hw hO₀ hi₀ π hσ hR h hm
    obtain ⟨l', h', hll', hR', hst', ⟨stop, hm'⟩, heq', hc'⟩ :=
      rel_roundTrips hk hkn hw hO₀ hi₀ π hσ hj _ _ _ hR1 hst1 hE
    obtain ⟨hR'', heq''⟩ := rel_close hk hkn hw hO₀ hi₀ π hσ hR' h' hst' hm'
    rw [hR.1.x]
    refine ⟨l' + 1, by omega, h', hR'', ?_, heq''.trans (heq'.trans heq1), ?_⟩
    · obtain ⟨b, -, -, hs'⟩ := PagingWithDelay.PMD.closeHole_spec (I).valid h' hm'
      rw [hs']
    · rw [← critCount_succ_of_not h' (by rw [hm']; simp), hc',
        ← critCount_succ_of_not h (by rw [hm]; simp)]

lemma rel_levelPass_aux (hσ : ValidInstance σ) :
    ∀ (c j : ℕ) (e : Execution n) (l : ℕ), j + c = (maxLevel I).toNat + 1 →
      RelEq hk hkn hw hO₀ hi₀ π σ e l →
      (snapAt I l).stage = (if (j : ℤ) ≤ maxLevel I then .examine j else .idle) →
      l ≤ (log I).length →
      ∃ l', l ≤ l' ∧ l' ≤ (log I).length ∧
        RelEq hk hkn hw hO₀ hi₀ π σ
          ((List.range' j c).foldl (fun a j => preemptiveService k w π σ j a) e) l' ∧
        (snapAt I l').stage = .idle ∧
        ((List.range' j c).foldl (fun a j => preemptiveService k w π σ j a) e).moves.map view ++
          tail I l' = e.moves.map view ++ tail I l ∧
        critCount I l' = critCount I l
  | 0, j, e, l, hjc, hR, hst, hl => by
    have hM := maxLevel_nonneg hk hkn hw hO₀ hi₀ π (σ := σ)
    have : ¬ (j : ℤ) ≤ maxLevel I := by omega
    rw [if_neg this] at hst
    exact ⟨l, le_rfl, hl, hR, hst, rfl, rfl⟩
  | c + 1, j, e, l, hjc, hR, hst, hl => by
    have hM := maxLevel_nonneg hk hkn hw hO₀ hi₀ π (σ := σ)
    have hj : (j : ℤ) ≤ maxLevel I := by omega
    rw [if_pos hj] at hst
    obtain ⟨l1, hl1, hl1', hR1, hst1, heq1, hc1⟩ := rel_level hk hkn hw hO₀ hi₀ π hσ hj hR hst
    have hst1' : (snapAt I l1).stage =
        (if ((j + 1 : ℕ) : ℤ) ≤ maxLevel I then .examine ((j + 1 : ℕ) : ℤ) else .idle) := by
      rw [hst1]
      unfold afterLevel
      push_cast
      by_cases hlt : (j : ℤ) < maxLevel I
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
    obtain ⟨l', hl', hl'', hR', hst', heq', hc'⟩ :=
      rel_levelPass_aux hσ c (j + 1) _ l1 (by omega) hR1 hst1' hl1'
    refine ⟨l', by omega, hl'', ?_, hst', ?_, hc'.trans hc1⟩
    · rw [List.range'_succ, List.foldl_cons]; exact hR'
    · rw [List.range'_succ, List.foldl_cons, heq', heq1]

/-- **The level pass** after a critical service. -/
lemma rel_levelPass (hσ : ValidInstance σ) {e : Execution n} {l : ℕ}
    (hR : RelEq hk hkn hw hO₀ hi₀ π σ e l) (hst : (snapAt I l).stage = .examine 0)
    (hl : l ≤ (log I).length) :
    ∃ l', l ≤ l' ∧ l' ≤ (log I).length ∧
      RelEq hk hkn hw hO₀ hi₀ π σ ((levels w).foldl (fun a j => preemptiveService k w π σ j a) e) l' ∧
      (snapAt I l').stage = .idle ∧
      ((levels w).foldl (fun a j => preemptiveService k w π σ j a) e).moves.map view ++
        tail I l' = e.moves.map view ++ tail I l ∧
      critCount I l' = critCount I l := by
  have hM := maxLevel_nonneg hk hkn hw hO₀ hi₀ π (σ := σ)
  rw [levels_eq hk hkn hw hO₀ hi₀ π (σ := σ), List.range_eq_range']
  refine rel_levelPass_aux hk hkn hw hO₀ hi₀ π hσ _ 0 e l (by omega) hR ?_ hl
  rw [if_pos (by simpa using hM)]
  simpa using hst

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Bridge` -/
section

/-!
# Simulation bridge

The platform's `run k w O₀ i₀ π σ` records exactly the moves of our log on `J = simInst …`
(`run_moves`), its budgets stay nonnegative (`run_budget_nonneg`), it starts in our initial
state (`run_initial`, `initialX_eq`) and its moves are chained (`run_chain`). These are the
statements of `Milestones/Sim/Spec.lean`, primed.

The proof is a forward simulation (`sim_run`): one iteration of the platform's `runFuel` (next
event, critical service, level pass) corresponds to an idle phase of our log (ticks and advances,
no platform move; `idle_phase`), a critical service (`nextEvent_of_critical`, `rel_critical`) and
our level loop (`rel_levelPass`). At the end of our log the platform has no next event
(`nextEvent_of_final`); the fuel `σ.length + 1` suffices since we make at most `σ.length`
critical services (`critCount_le`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD
open PagingWithDelay.PMD (snapAt moveAt log Snap Stage minLevel)

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
  {σ : Instance n}

local notation "I" => J hk hkn hw hO₀ hi₀ π σ

lemma runFuel_succ (f : ℕ) (e : Execution n) :
    runFuel k w π σ (f + 1) e =
      match nextEvent k w π e σ with
      | none => e
      | some (t, p) =>
        runFuel k w π σ f
          ((levels w).foldl (fun a j => preemptiveService k w π σ j a) (criticalService k w σ e t p)) :=
  rfl

/-- **The simulation**: from an idle index related to `e`, the platform's `runFuel` appends
exactly the moves recorded by the rest of our log, with nonnegative budgets. -/
lemma sim_run (hσ : ValidInstance σ) :
    ∀ (f i : ℕ) (e : Execution n), Rel hk hkn hw hO₀ hi₀ π σ e i → i ≤ (log I).length →
      (snapAt I i).stage = .idle → critCount I i < f →
      (runFuel k w π σ f e).moves.map view = e.moves.map view ++ tail I i ∧
        ∀ m ∈ (runFuel k w π σ f e).moves, ∀ j, 0 ≤ m.after.budget j
  | 0, i, e, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, i, e, hR, hi, hst, hf => by
    obtain ⟨j, hij, hjl, hRj, hstj, htj, hcj, hend⟩ := idle_phase hk hkn hw hO₀ hi₀ π hσ hR hi hst
    rcases hend with rfl | ⟨h, p, hm⟩
    · rw [runFuel_succ, nextEvent_of_final hk hkn hw hO₀ hi₀ π hσ hRj]
      refine ⟨?_, hR.moves_budget⟩
      rw [htj, tail_length, List.append_nil]
    · rw [runFuel_succ, nextEvent_of_critical hk hkn hw hO₀ hi₀ π hσ hRj h hm]
      obtain ⟨hR1, ht1, heq1⟩ := rel_critical hk hkn hw hO₀ hi₀ π hσ hRj h hm
      have hst1 : (snapAt I (j + 1)).stage = .examine 0 := by
        obtain ⟨-, -, hs⟩ := PagingWithDelay.PMD.critical_spec (I).valid h hm
        rw [hs, minLevel_eq hk hkn hw hO₀ hi₀ π]
      obtain ⟨l', hl', hl'', hR2, hst2, heq2, hc2⟩ :=
        rel_levelPass hk hkn hw hO₀ hi₀ π hσ ⟨hR1, ht1⟩ hst1 (by omega)
      have hc := critCount_succ_of_critical h hm
      obtain ⟨ih1, ih2⟩ := sim_run hσ f l' _ hR2.1 hl'' hst2 (by omega)
      refine ⟨?_, ih2⟩
      rw [ih1, heq2, heq1, htj]

/-- The run when our log is not empty: from index `1` (after the first tick). -/
lemma run_spec (hσ : ValidInstance σ) :
    (run k w O₀ i₀ π σ).moves.map view = logMoves I ∧
      ∀ m ∈ (run k w O₀ i₀ π σ).moves, ∀ j, 0 ≤ m.after.budget j := by
  unfold run
  by_cases hl : log I = []
  · rw [runFuel_succ,
      nextEvent_start_of_log_nil hk hkn hw hO₀ hi₀ π hσ hl]
    refine ⟨?_, by simp [start]⟩
    simp [start, logMoves, hl]
  · have h0 : 0 < (log I).length := List.length_pos_iff.2 hl
    obtain ⟨⟨t, ht⟩, hst1⟩ := first_tick_idle h0
    have hR := rel_one hk hkn hw hO₀ hi₀ π hσ h0
    have hc0 : critCount I 0 = critCount I 1 := critCount_succ_of_not h0 (by rw [ht]; simp)
    have hcle := critCount_le (input := I)
    rw [J_requests, List.length_map] at hcle
    obtain ⟨h1, h2⟩ := sim_run hk hkn hw hO₀ hi₀ π hσ (σ.length + 1) 1 _ hR h0 hst1 (by omega)
    refine ⟨?_, h2⟩
    rw [h1, ← tail_zero, tail_succ h0, ht]
    simp [start, entryMoves_tick]

/-- **The bridge**: the platform run records exactly the moves of our log. -/
theorem run_moves (hσ : ValidInstance σ) :
    (run k w O₀ i₀ π σ).moves.map view = logMoves (J hk hkn hw hO₀ hi₀ π σ) :=
  (run_spec hk hkn hw hO₀ hi₀ π hσ).1

include hk hkn hw hO₀ hi₀ in
/-- Budgets of the platform run stay nonnegative (for all `j : ℕ`, not only the levels).
(Unlike `Spec.run_budget_nonneg`, whose statement does not mention them, this takes the standing
hypotheses `hk hkn hw hO₀ hi₀` explicitly via `include`.) -/
theorem run_budget_nonneg (hσ : ValidInstance σ) :
    ∀ m ∈ (run k w O₀ i₀ π σ).moves, ∀ j, 0 ≤ m.after.budget j :=
  (run_spec hk hkn hw hO₀ hi₀ π hσ).2

/-- The platform run starts in our initial state at time `0`, with zero claims and budgets. -/
theorem run_initial :
    (run k w O₀ i₀ π σ).initial = ⟨0, initialX k O₀ i₀, fun _ => 0, fun _ => 0⟩ := by
  unfold run
  rw [runFuel_initial]
  rfl

/-- The moves of the platform run are chained: each starts where the previous one ended, and the
current snapshot is the end of the last move. -/
theorem run_chain :
    (run k w O₀ i₀ π σ).moves.map (fun m => m.before) =
        ((run k w O₀ i₀ π σ).initial :: (run k w O₀ i₀ π σ).moves.map (fun m => m.after)).dropLast ∧
      (run k w O₀ i₀ π σ).current =
        ((run k w O₀ i₀ π σ).moves.map (fun m => m.after)).getLastD (run k w O₀ i₀ π σ).initial :=
  chain_runFuel k w π σ _ _ (chain_start k O₀ i₀)

/-- The platform's initial state is ours. -/
theorem initialX_eq :
    initialX k O₀ i₀ = PagingWithDelay.PMD.initialState (J hk hkn hw hO₀ hi₀ π σ) := by
  funext i
  simp only [initialX, PagingWithDelay.PMD.initialState, PagingWithDelay.PMD.initialPage,
    J_initialCache, J_startPage, J_delta, J_cacheSize, Option.some.injEq]
  by_cases h1 : i ∈ O₀
  · simp [h1]
  · by_cases h2 : i = i₀
    · subst h2
      simp only [h1, if_false, if_true]
      unfold delta
      have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    · simp [h1, h2, Ne.symm h2]

end

end PagingDelay.PMD.Sim
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

/-! ## Inlined from `Milestones.Sim.Excess` -/
section

/-!
# The offline dictionary for Propositions 21 and 30

For a `LazyFeasible` platform schedule `O`, `toSteps O` is a comparator of `PagingWithDelay` in
swap form, feasible with the platform's service times, of cost `totalCost w O₀ O σ`
(`offline_comparator`). Its cache after all steps at time `t` is the platform's
`cacheAfter O₀ O t` (`cacheAt_toSteps`), and the platform's `excess` of the run is the sum of the
excesses `excessAt` of the entries of our log (`excess_eq`): a critical move is a critical service
at the current time `entryTime = now`, from a rest state, and `serviceExcess` (natural levels `j`
with `w_p ≤ 2^j < w_min`, `bandLength`) is the sum of `levelLen` over `excessLevels`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD

/-! ### Lazy schedules -/

/-- The cache before event `j` of `s` started from `c`. -/
def prevCache {n : ℕ} (c : Finset (Fin n)) (s : Schedule n) : ℕ → Finset (Fin n)
  | 0 => c
  | j + 1 => (s[j]?.map CacheEvent.cache).getD c

lemma lazyFrom_getElem {n : ℕ} : ∀ (c : Finset (Fin n)) (s : Schedule n), LazyFrom c s →
    ∀ (j : ℕ) (hj : j < s.length), ∃ p ∈ prevCache c s j, ∃ q, q ∉ prevCache c s j ∧
      s[j].cache = insert q ((prevCache c s j).erase p)
  | c, [], _, j, hj => by simp at hj
  | c, e :: es, h, 0, hj => by simpa [prevCache] using h.1
  | c, e :: es, h, j + 1, hj => by
    have hj' : j < es.length := by simpa using hj
    have hprev : prevCache c (e :: es) (j + 1) = prevCache e.cache es j := by
      cases j <;> simp (disch := omega) [prevCache]
    rw [hprev]
    simpa using lazyFrom_getElem e.cache es h.2 j hj'

lemma lazyFrom_card {n k : ℕ} : ∀ (c : Finset (Fin n)) (s : Schedule n), LazyFrom c s →
    c.card = k → ∀ e ∈ s, e.cache.card = k
  | c, [], _, _, e, he => by simp at he
  | c, f :: fs, h, hc, e, he => by
    obtain ⟨⟨p, hp, q, hq, hf⟩, h'⟩ := h
    have hfc : f.cache.card = k := by
      rw [hf, PagingWithDelay.Schedule.NF.swap_card hq hp, hc]
    rcases List.mem_cons.1 he with rfl | he
    · exact hfc
    · exact lazyFrom_card f.cache fs h' hfc e he

lemma cacheAfter_card {n k : ℕ} {O₀ : Finset (Fin n)} {O : Schedule n} (hl : LazyFrom O₀ O)
    (hO₀ : O₀.card = k) (t : ℝ) : (cacheAfter O₀ O t).card = k := by
  unfold cacheAfter
  rw [List.getLastD_eq_getLast?]
  cases h : ((O.filter fun e => decide (e.time ≤ t)).map CacheEvent.cache).getLast? with
  | none => simpa using hO₀
  | some c =>
    simp only [Option.getD_some]
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_of_getLast? h)
    exact lazyFrom_card O₀ O hl hO₀ e (List.mem_of_mem_filter he)

/-! ### The comparator -/

section

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
  {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)

/-- The platform's cache after all events at time `t` is our `cacheAt`. -/
lemma cacheAt_toSteps (σ : Instance n) {O : Schedule n}
    (hs : O.Pairwise fun e f => e.time ≤ f.time) (t : ℝ) :
    PagingWithDelay.Schedule.cacheAt (J hk hkn hw hO₀ hi₀ π σ) (Thm1.toSteps O) t =
      cacheAfter O₀ O t := by
  have hfilt := PagingWithDelay.Rounding.filter_eq_take
    (P := fun e : CacheEvent n => decide (e.time ≤ t))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hs
  have hlen : ((Thm1.toSteps O).filter fun step => decide (step.time ≤ t)).length =
      (O.filter fun e => decide (e.time ≤ t)).length := by
    simp [Thm1.toSteps, List.filter_map, Function.comp_def]
  unfold PagingWithDelay.Schedule.cacheAt cacheAfter
  rw [hlen, hfilt]
  set m := (O.filter fun e => decide (e.time ≤ t)).length with hm
  have hms : m ≤ O.length := List.length_filter_le _ _
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; rfl
  · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hj : m' < O.length := by omega
    rw [List.length_take, min_eq_left hms, hm', List.getLastD_eq_getLast?, List.getLast?_map,
      List.getLast?_take]
    simp [PagingWithDelay.Schedule.cacheBeforeStep, Thm1.toSteps,
      List.getElem?_eq_getElem hj]

/-- A lazy platform schedule is in swap form. -/
lemma swapForm_toSteps (σ : Instance n) {O : Schedule n}
    (hs : O.Pairwise fun e f => e.time ≤ f.time) (hl : LazyFrom O₀ O) :
    PagingWithDelay.Schedule.SwapForm (J hk hkn hw hO₀ hi₀ π σ) (Thm1.toSteps O) := by
  refine ⟨by simpa [Thm1.toSteps, List.pairwise_map] using hs, fun j hj => ?_⟩
  have hj' : j < O.length := by simpa [Thm1.toSteps] using hj
  obtain ⟨p, hp, q, hq, he⟩ := lazyFrom_getElem O₀ O hl j hj'
  have hprev : PagingWithDelay.Schedule.cacheBeforeStep (J hk hkn hw hO₀ hi₀ π σ)
      (Thm1.toSteps O) j = prevCache O₀ O j := by
    cases j
    · rfl
    · simp (disch := omega) [PagingWithDelay.Schedule.cacheBeforeStep, prevCache, Thm1.toSteps]
  rw [hprev]
  exact ⟨q, p, hq, hp, by simpa [Thm1.toSteps] using he⟩

/-- **The comparator**: a lazy feasible platform schedule of finite cost is a comparator of
`PagingWithDelay` (swap form, feasible with service times `τ`) of the same cost. -/
theorem offline_comparator {σ : Instance n} (hσ : ValidInstance σ) {O : Schedule n}
    (hO : LazyFeasible k O₀ O σ) (hfin : totalCost w O₀ O σ ≠ ⊤) :
    ∃ τ : PagingWithDelay.Request (Fin n) → ℝ,
      (∀ ρ ∈ (J hk hkn hw hO₀ hi₀ π σ).requests, ρ.arrival ≤ τ ρ) ∧
      PagingWithDelay.Schedule.SwapForm (J hk hkn hw hO₀ hi₀ π σ) (Thm1.toSteps O) ∧
      (Thm1.toSteps O).FeasibleBy (J hk hkn hw hO₀ hi₀ π σ) τ ∧
      ENNReal.ofReal ((Thm1.toSteps O).fetchCost (J hk hkn hw hO₀ hi₀ π σ) +
        PagingWithDelay.Schedule.totalDelay (J hk hkn hw hO₀ hi₀ π σ) τ) =
        totalCost w O₀ O σ := by
  obtain ⟨hvalid, hl, -⟩ := hO
  obtain ⟨τ, hF, hST, hcost⟩ := Thm1.exists_costWith hk hkn (Bridge.weight_pos_of_PMDWeights hw)
    hO₀ hσ hvalid hfin
  refine ⟨τ, fun ρ hρ => (hST ρ hρ).1, swapForm_toSteps hk hkn hw hO₀ hi₀ π σ hvalid.2.2 hl,
    ⟨hF.chronological, hF.capacity, fun ρ hρ => ⟨τ ρ, (hST ρ hρ).1, le_rfl, (hST ρ hρ).2⟩⟩,
    hcost⟩

/-! ### Excess of one critical service -/

lemma minWeight_le {n : ℕ} (w : Fin n → ℝ) {O : Finset (Fin n)} {q : Fin n} (hq : q ∈ O) :
    minWeight w O ≤ w q := by
  unfold minWeight
  rw [← Finset.mem_toList] at hq
  generalize O.toList = l at *
  induction l with
  | nil => simp at hq
  | cons x l ih =>
    cases l with
    | nil => simp_all
    | cons y l =>
      simp only [List.map_cons, List.foldr_cons, Option.getD_some] at ih ⊢
      rcases List.mem_cons.1 hq with rfl | hq
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih hq)

/-- `serviceExcess` is the sum of `levelLen` over `excessLevels`. -/
lemma serviceExcess_eq (σ : Instance n) (S : PagingWithDelay.Schedule (Fin n)) (t : ℝ)
    {x : Fin n → ℝ} (hx : StateValid k x) (p : Fin n)
    (hc : (PagingWithDelay.Schedule.cacheAt (J hk hkn hw hO₀ hi₀ π σ) S t).Nonempty) :
    serviceExcess k w x p (PagingWithDelay.Schedule.cacheAt (J hk hkn hw hO₀ hi₀ π σ) S t) =
      ∑ e ∈ PagingWithDelay.PMD.excessLevels (J hk hkn hw hO₀ hi₀ π σ) S p t,
        PagingWithDelay.PMD.levelLen (J hk hkn hw hO₀ hi₀ π σ) x p e := by
  set I := J hk hkn hw hO₀ hi₀ π σ with hI
  set c := PagingWithDelay.Schedule.cacheAt I S t with hcdef
  set E := PagingWithDelay.PMD.excessLevels I S p t with hE
  have hw' := Bridge.weight_pos_of_PMDWeights hw
  have hv : I.Valid := I.valid
  obtain ⟨qmin, hqmin, hmin⟩ := Bridge.exists_minWeight_eq w hc
  have h2pow : ∀ j : ℕ, PagingWithDelay.PMD.levelWeight (j : ℤ) = level j :=
    fun j => zpow_natCast _ _
  set L' := (levels w).filter (fun j => decide (w p ≤ level j ∧ level j < minWeight w c))
    with hL'
  -- both `j ≤ maxLevel` and `j ∈ levels w` follow from `2^j < w_min`
  have hmemE : ∀ j : ℕ, (j : ℤ) ∈ E ↔ j ∈ L' := by
    intro j
    have hmw : (∀ q ∈ c, level j < I.weight q) ↔ level j < minWeight w c :=
      ⟨fun h => hmin ▸ h qmin hqmin, fun h q hq => h.trans_le (minWeight_le w hq)⟩
    have hlt : level j < minWeight w c → (j : ℤ) ≤ PagingWithDelay.PMD.maxLevel I ∧
        j ∈ levels w := fun h => by
      rw [hmin] at h
      refine ⟨?_, Bridge.mem_levels hw.1 qmin h.le⟩
      have := mt (PagingWithDelay.PMD.level_le_iff hv qmin j).1 (by rw [h2pow]; exact not_le.2 h)
      exact (not_le.1 this).le.trans (PagingWithDelay.PMD.le_maxLevel qmin)
    simp only [hE, PagingWithDelay.PMD.excessLevels, Finset.mem_filter, Finset.mem_Icc, hL',
      List.mem_filter, decide_eq_true_eq, ← hcdef, PagingWithDelay.PMD.level_le_iff hv, h2pow,
      hmw]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨(hlt h3).2, h1, h3⟩
    · rintro ⟨-, h1, h3⟩; exact ⟨⟨h1, (hlt h3).1⟩, h3⟩
  have hp0 : 0 ≤ PagingWithDelay.PMD.level I p := by
    obtain ⟨m, hm⟩ := hw.1 p
    by_contra h
    have h1 := (PagingWithDelay.PMD.level_le_iff hv p (-1)).1 (by omega)
    have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    change w p ≤ _ at h1
    norm_num [PagingWithDelay.PMD.levelWeight, hm] at h1
    linarith
  have hE0 : ∀ e ∈ E, 0 ≤ e := fun e he => by
    simp only [hE, PagingWithDelay.PMD.excessLevels, Finset.mem_filter, Finset.mem_Icc] at he
    exact hp0.trans he.1.1
  have hnd : L'.Nodup := List.nodup_range.filter _
  have himg : L'.toFinset = E.image Int.toNat := by
    ext j
    simp only [List.mem_toFinset, Finset.mem_image]
    constructor
    · intro hj; exact ⟨j, (hmemE j).2 hj, by simp⟩
    · rintro ⟨e, he, rfl⟩
      rw [← hmemE, Int.toNat_of_nonneg (hE0 e he)]
      exact he
  set Sx := PagingWithDelay.PMD.serviceEnd (Bridge.inst n k hk hkn w hw') x p
  have hS0 : 0 ≤ Sx := PagingWithDelay.PMD.serviceEnd_nonneg' _ _
  have hpl : pathLength k w x p = Sx := Bridge.pathLength_eq hk hkn hw' hx p
  calc serviceExcess k w x p c
      = (L'.map fun j => bandLength k Sx (level j)).sum := by
        unfold serviceExcess; rw [hpl]
    _ = ∑ j ∈ L'.toFinset, bandLength k Sx (level j) := (List.sum_toFinset _ hnd).symm
    _ = ∑ e ∈ E, bandLength k Sx (level e.toNat) := by
        rw [himg, Finset.sum_image]
        intro a ha b hb hab
        have := hE0 a ha
        have := hE0 b hb
        omega
    _ = ∑ e ∈ E, PagingWithDelay.PMD.levelLen I x p e := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Bridge.bandLength_eq hk hkn hw' Sx _ hS0 (by unfold level; positivity),
          ← h2pow, Int.toNat_of_nonneg (hE0 e he)]
        rfl

/-! ### The excess of the run -/

/-- **The platform excess of the run** is the sum of the excesses of the entries of our log,
against the comparator `toSteps O`. -/
theorem excess_eq {σ : Instance n} (hσ : ValidInstance σ) {O : Schedule n}
    (hs : O.Pairwise fun e f => e.time ≤ f.time) (hl : LazyFrom O₀ O) :
    excess k w O₀ O (run k w O₀ i₀ π σ) =
      ∑ i ∈ Finset.range (PagingWithDelay.PMD.log (J hk hkn hw hO₀ hi₀ π σ)).length,
        PagingWithDelay.PMD.excessAt (J hk hkn hw hO₀ hi₀ π σ) (Thm1.toSteps O) i := by
  have hw' := Bridge.weight_pos_of_PMDWeights hw
  let g : MoveKind n × (Fin n → ℝ) × (Fin n → ℝ) × ℝ → ℝ := fun v =>
    match v.1 with
    | .critical p =>
      if p ∈ cacheAfter O₀ O v.2.2.2 then 0 else serviceExcess k w v.2.1 p (cacheAfter O₀ O v.2.2.2)
    | _ => 0
  have h1 : excess k w O₀ O (run k w O₀ i₀ π σ) =
      (((run k w O₀ i₀ π σ).moves.map view).map g).sum := by
    unfold excess; rw [List.map_map]; rfl
  rw [h1, run_moves hk hkn hw hO₀ hi₀ π hσ, logMoves, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_map, ← Fin.sum_univ_fun_getElem, Finset.sum_range]
  set I := J hk hkn hw hO₀ hi₀ π σ with hI
  refine Finset.sum_congr rfl fun ⟨i, hi'⟩ _ => ?_
  unfold PagingWithDelay.PMD.excessAt
  rw [dif_pos hi']
  have hsnap : PagingWithDelay.PMD.snapAt I i = ((PagingWithDelay.PMD.log I)[i]).1 := by
    unfold PagingWithDelay.PMD.snapAt; rw [dif_pos hi']
  change ((entryMoves I _ (PagingWithDelay.PMD.moveAt i hi')).map g).sum = _
  rcases hm : PagingWithDelay.PMD.moveAt i hi' with t | t | p | e | e | ⟨e, ρ⟩ | ⟨e, st⟩
  case critical =>
    obtain ⟨-, -, hrest, -, htime⟩ := PagingWithDelay.PMD.critical_facts I.valid hi' hm
    have hx : StateValid k (PagingWithDelay.PMD.snapAt I i).x :=
      (Bridge.isRest_iff hk hkn hw' _).1 hrest
    have hct := cacheAt_toSteps hk hkn hw hO₀ hi₀ π σ hs (PagingWithDelay.PMD.snapAt I i).now
    rw [← hI] at hct
    have hne : (PagingWithDelay.Schedule.cacheAt I (Thm1.toSteps O)
        (PagingWithDelay.PMD.entryTime I i)).Nonempty := by
      rw [htime, hct, ← Finset.card_pos, cacheAfter_card hl hO₀]; omega
    simp only [entryMoves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, g]
    rw [← hsnap, htime, ← hct]
    split_ifs with hp
    · rfl
    · rw [← htime, serviceExcess_eq hk hkn hw hO₀ hi₀ π σ _ _ hx p hne]
  all_goals simp only [entryMoves]; try split
  all_goals simp [g]

end

end PagingDelay.PMD.Sim
end

/-! ## Inlined from `Milestones.Sim.Prop30` -/
section

/-!
# Proposition 30: total excess

`excess_eq` turns the platform's excess into `∑ excessAt` against the comparator `toSteps O`
(`offline_comparator`), and `MainProof.excess_le` bounds it by
`L·X + 3/2 (X + w(O₀)) + (L + 4)(X + w(O₀)) ≤ 8 L X + 7 L ∑ wᵢ` with `X` the cost of `O`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD

lemma powerOfTwo_J {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
    {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (σ : Instance n) : (J hk hkn hw hO₀ hi₀ π σ).PowerOfTwoWeights := fun i => by
  obtain ⟨m, hm⟩ := hw.1 i
  exact ⟨m, by show w i = _; rw [hm]; simp⟩

/-- The comparator's cost `X ≥ 0` and the weight of the initial cache. -/
lemma comparator_facts {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) {w : Fin n → ℝ} (hw : PMDWeights w)
    {O₀ : Finset (Fin n)} (hO₀ : O₀.card = k) {i₀ : Fin n} (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (σ : Instance n) (S : PagingWithDelay.Schedule (Fin n)) (τ : PagingWithDelay.Request (Fin n) → ℝ)
    (hτ : ∀ ρ ∈ (J hk hkn hw hO₀ hi₀ π σ).requests, ρ.arrival ≤ τ ρ) :
    0 ≤ S.fetchCost (J hk hkn hw hO₀ hi₀ π σ) +
        PagingWithDelay.Schedule.totalDelay (J hk hkn hw hO₀ hi₀ π σ) τ ∧
      0 ≤ ∑ p ∈ (J hk hkn hw hO₀ hi₀ π σ).initialCache, (J hk hkn hw hO₀ hi₀ π σ).weight p ∧
      ∑ p ∈ (J hk hkn hw hO₀ hi₀ π σ).initialCache, (J hk hkn hw hO₀ hi₀ π σ).weight p ≤
        ∑ i, w i := by
  have hv := (J hk hkn hw hO₀ hi₀ π σ).valid
  have hw' := Bridge.weight_pos_of_PMDWeights hw
  refine ⟨add_nonneg (PagingWithDelay.PMD.MainProof.costFrom_nonneg _ (fun p => (hw' p).le) _ _)
      (PagingWithDelay.Schedule.totalDelay_nonneg hv hτ),
    Finset.sum_nonneg fun p _ => (hw' p).le,
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => (hw' p).le⟩

/-- **Proposition 30**. -/
theorem proposition_30' :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n), ∀ (σ : Instance n) (hσ : ValidInstance σ), ∀ O : Schedule n,
      LazyFeasible k O₀ O σ →
      ENNReal.ofReal (excess k w O₀ O (run k w O₀ i₀ π σ)) ≤
        ENNReal.ofReal (C₁ * logFactor k) * totalCost w O₀ O σ +
        ENNReal.ofReal (C₂ * logFactor k * ∑ i, w i) := by
  refine ⟨8, 7, by norm_num, by norm_num, ?_⟩
  intro n k hk hkn w hw O₀ hO₀ i₀ hi₀ π σ hσ O hO
  have hL := PagingWithDelay.Instance.one_le_L (J hk hkn hw hO₀ hi₀ π σ).valid
  change 1 ≤ logFactor k at hL
  by_cases hfin : totalCost w O₀ O σ = ⊤
  · rw [hfin, ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    simp
  obtain ⟨τ, hτ, hSw, hF, hcost⟩ := offline_comparator hk hkn hw hO₀ hi₀ π hσ hO hfin
  obtain ⟨hX, hW0, hW⟩ := comparator_facts hk hkn hw hO₀ hi₀ π σ (Thm1.toSteps O) τ hτ
  have hex := PagingWithDelay.PMD.MainProof.excess_le (J hk hkn hw hO₀ hi₀ π σ).valid
    (powerOfTwo_J hk hkn hw hO₀ hi₀ π σ) hτ hSw hF
  change _ ≤ logFactor k * _ + _ + (logFactor k + 4) * _ at hex
  rw [excess_eq hk hkn hw hO₀ hi₀ π hσ hO.1.2.2 hO.2.1, ← hcost,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

end PagingDelay.PMD.Sim
end
open PagingDelay.PMD in
theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n), ∀ (σ : Instance n) (hσ : ValidInstance σ), ∀ O : Schedule n,
      LazyFeasible k O₀ O σ →
      ENNReal.ofReal (excess k w O₀ O (run k w O₀ i₀ π σ)) ≤
        ENNReal.ofReal (C₁ * logFactor k) * totalCost w O₀ O σ +
        ENNReal.ofReal (C₂ * logFactor k * ∑ i, w i) :=
  PagingDelay.PMD.Sim.proposition_30'
