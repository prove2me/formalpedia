-- Prove2me | solution 1 for TenChallenges.challenge_10_losingInducedBall
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:23:58.791159+00:00
-- url     : https://prove2.me/submissions/2dac3820-97cc-4b05-be02-e75470a946c4

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Family

universe u v

/- Inlined from Continuation/UnfriendlyClockContinuity.lean. -/
/-!
# Continuity of unfriendly-game winning clocks

Challenger announces the residual clock before Partitioner chooses a response.
Consequently, winning clocks are closed under suprema. In particular, winning
at every finite clock is equivalent to winning at the first infinite clock.
Neither statement asserts that those clocks are winning on every graph.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V) (f : V → Option Bool)

/-- Winning strategies at every clock of a family give a strategy at their supremum. -/
theorem partitionerWins_iSup {ι : Type v} (α : ι → Ordinal.{v})
    (h : ∀ i, PartitionerWins G f (α i)) :
    PartitionerWins G f (iSup α) := by
  rw [PartitionerWins]
  intro x β hβ
  obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.mp hβ
  have hwin := h i
  rw [PartitionerWins] at hwin
  exact hwin x β hi

/-- Winning at the first infinite clock is exactly winning at every finite clock. -/
theorem partitionerWins_omega_iff :
    PartitionerWins G f (Ordinal.omega0 : Ordinal.{v}) ↔
      ∀ n : ℕ, PartitionerWins G f (n : Ordinal.{v}) := by
  constructor
  · intro h n
    rw [PartitionerWins] at h ⊢
    exact fun x β hβ => h x β (hβ.trans (Ordinal.natCast_lt_omega0 n))
  · intro h
    rw [PartitionerWins]
    intro x β hβ
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hβ
    have hwin := h (n + 1)
    rw [PartitionerWins] at hwin
    exact hwin x n (Nat.cast_lt.mpr (Nat.lt_succ_self n))

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyBoundedResponses.lean. -/
/-!
# Bounded responses for finite clocks

An existing winning response can be reduced to the current assignments, the
queried vertex, and witnesses balancing the coloured same-colour neighbours.
A winning strategy from the larger response also works after forgetting some
colours.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The number of assigned vertices of a finite partial colouring. -/
noncomputable def assignedCount (f : V → Option Bool) : ℕ :=
  ({x | f x ≠ none} : Set V).ncard

/-- A strategy from a larger assignment can be used after forgetting colours. -/
theorem partitionerWins_of_restriction {f p : V → Option Bool} {α : Ordinal.{v}}
    (hfp : Extends f p) (hp : PartitionerWins G p α) :
    PartitionerWins G f α := by
  rw [PartitionerWins] at hp ⊢
  intro x β hβ
  obtain ⟨g, hg, hw⟩ := hp x β hβ
  exact ⟨g, ⟨fun y b hb => hg.1 y b (hfp y b hb), hg.2⟩, hw⟩

/-- Extract a legal response with at most twice the previous domain size plus
one assigned vertex, preserving agreement with the given extension. -/
theorem bounded_response_of_unfriendly {f p : V → Option Bool}
    (hf : HasFiniteDomain f) (hfp : Extends f p)
    (x : V) (hp : UnfriendlyAt G p x) :
    ∃ g, IsLegalResponse G f g x ∧ Extends g p ∧
      assignedCount g ≤ 2 * assignedCount f + 1 := by
  classical
  obtain ⟨b, hpx, hcard⟩ := hp
  let D : Set V := {y | f y ≠ none}
  let S : Set V := G.neighborSet x ∩ f ⁻¹' {some b}
  have hSD : S ⊆ D := fun _ hy => Option.ne_none_iff_exists'.mpr ⟨b, hy.2⟩
  have hsameInP : S ⊆ G.neighborSet x ∩ p ⁻¹' {some b} :=
    fun y hy => ⟨hy.1, hfp y b hy.2⟩
  obtain ⟨e⟩ := (Cardinal.le_def S (NeighColored G p x (some (!b)))).mp
    ((Cardinal.mk_le_mk_of_subset hsameInP).trans hcard)
  let : Finite S := (hf.subset hSD).to_subtype
  let T : Set V := Set.range fun y : S => (e y).val
  have hT : T.Finite := Set.finite_range _
  have hTcolour : ∀ y ∈ T, p y = some (!b) :=
    fun _ ⟨z, hz⟩ => hz ▸ (e z).property.2
  let g : V → Option Bool := fun y => if y = x ∨ y ∈ T then p y else f y
  have hfg : Extends f g := fun y c hy =>
    (Classical.em (y = x ∨ y ∈ T)).elim
      (fun hh => (if_pos hh).trans (hfp y c hy)) (fun hh => (if_neg hh).trans hy)
  have hgp : Extends g p := fun y c hy =>
    (Classical.em (y = x ∨ y ∈ T)).elim
      (fun hh => (if_pos hh).symm.trans hy) (fun hh => hfp y c ((if_neg hh).symm.trans hy))
  have hdomain : {y | g y ≠ none} ⊆ insert x (D ∪ T) := by
    intro y hy
    by_cases H : y = x ∨ y ∈ T
    · exact H.imp_right Or.inr
    · exact Or.inr (Or.inl (fun h => hy ((if_neg H).trans h)))
  have hdomFin : (insert x (D ∪ T)).Finite := (hf.union hT).insert x
  have hsizeT : T.ncard ≤ D.ncard :=
    (Set.ncard_range_of_injective (Subtype.val_injective.comp e.injective)).le.trans
      (Set.ncard_le_ncard hSD hf)
  have hsize : assignedCount g ≤ 2 * assignedCount f + 1 := by
    have hU := Set.ncard_union_le D T
    refine (Set.ncard_le_ncard hdomain hdomFin).trans ((Set.ncard_insert_le x _).trans ?_)
    change (D ∪ T).ncard + 1 ≤ 2 * D.ncard + 1
    omega
  have hsame : (G.neighborSet x ∩ g ⁻¹' {some b}) ⊆ S := by
    rintro y ⟨ha, hy⟩
    refine ⟨ha, ?_⟩
    by_cases H : y = x ∨ y ∈ T
    · refine H.elim (fun h => (G.irrefl (h ▸ ha)).elim) fun ht => ?_
      have hpEq : p y = some b := (if_pos H).symm.trans hy
      exact ((Bool.not_eq_self b).mp (Option.some.inj ((hTcolour y ht).symm.trans hpEq))).elim
    · exact (if_neg H).symm.trans hy
  let E : S ↪ NeighColored G g x (some (!b)) :=
    ⟨fun s => ⟨(e s).val, (e s).property.1,
      (if_pos (Or.inr ⟨s, rfl⟩)).trans (e s).property.2⟩,
      fun s t h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g x (some (!b)) => z.val) h))⟩
  exact ⟨g, ⟨hfg, hdomFin.subset hdomain, b, (if_pos (Or.inl rfl)).trans hpx,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩, hgp, hsize⟩

/-- The natural-clock game in which each move uses a bounded response and drops
the clock by exactly one. -/
def BoundedFiniteWins (f : V → Option Bool) : ℕ → Prop
  | 0 => True
  | n + 1 => ∀ x : V, ∃ g, IsLegalResponse G f g x ∧
      assignedCount g ≤ 2 * assignedCount f + 1 ∧ BoundedFiniteWins g n

/-- The bounded natural-clock game and the original game have the same winning
positions with finite assigned domain. -/
theorem partitionerWins_natCast_iff_boundedFiniteWins (f : V → Option Bool)
    (hf : HasFiniteDomain f) (n : ℕ) :
    PartitionerWins G f (n : Ordinal.{v}) ↔ BoundedFiniteWins G f n := by
  induction n generalizing f
  case zero =>
    rw [PartitionerWins]
    simp [BoundedFiniteWins]
  case succ n ih =>
    rw [BoundedFiniteWins]
    constructor
    · intro hw x
      rw [PartitionerWins] at hw
      obtain ⟨p, hlegal, hwin⟩ := hw x (n : Ordinal.{v}) (Nat.cast_lt.mpr (Nat.lt_succ_self n))
      obtain ⟨g, hg, hgp, hsize⟩ := bounded_response_of_unfriendly G hf hlegal.1 x hlegal.2.2
      exact ⟨g, hg, hsize, (ih g hg.2.1).mp (partitionerWins_of_restriction G hgp hwin)⟩
    · intro hw
      rw [PartitionerWins]
      intro x β hβ
      obtain ⟨g, hg, _, hwin⟩ := hw x
      have h : PartitionerWins G g (n : Ordinal.{v}) := (ih g hg.2.1).mpr hwin
      rw [Nat.cast_add_one, ← Order.succ_eq_add_one] at hβ
      refine ⟨g, hg, ?_⟩
      rw [PartitionerWins] at h ⊢
      exact fun y γ hγ => h y γ (hγ.trans_le (Order.lt_succ_iff.mp hβ))

/-- The first infinite clock is equivalent to winning all bounded finite games. -/
theorem partitionerWins_omega_iff_boundedFiniteWins (f : V → Option Bool)
    (hf : HasFiniteDomain f) :
    PartitionerWins G f (Ordinal.omega0 : Ordinal.{v}) ↔ ∀ n, BoundedFiniteWins G f n :=
  (partitionerWins_omega_iff G f).trans (forall_congr' (partitionerWins_natCast_iff_boundedFiniteWins G f hf))

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyLocalResponses.lean. -/
/-!
# Local responses in the unfriendly partition game

New assignments are needed only at the queried vertex and its neighbours.
This keeps the influence of a move within a controlled distance.

## Bounding the radius of a first losing arena

Suppose the empty position in a graph first loses at natural clock n. Use the
bounded local game for this argument. Choose a losing first query a. The first
response assigns exactly a, since the size bound is one and a legal response
assigns the queried vertex. Its resulting position loses at clock n - 1.

At any subsequent losing position, use its least losing clock k. The empty
position still wins at k, and the current position wins at k - 1. The theorem
exists_near_losing_query gives a losing query at walk distance at most
separation (k - 1) + 1 from a previously assigned vertex. Every new assignment
in the local game is at this query or a neighbour. Thus one such move increases
the radius of the assigned domain about a by at most separation (k - 1) + 2.

The least losing clocks of successive positions decrease strictly. Since
separation j = 2^(j+1) - 2, the total radius increase from the singleton is
at most the sum of separation (k - 1) + 2 for 1 ≤ k ≤ n - 1. This sum is
2^n - 2. The same bound includes the queries, including a final query with
no response.

Induce the graph on the ball of radius 2^n - 2 about a in the original graph.
Any bounded local reply in this induced graph extends by the unassigned value
to a bounded local reply in the original graph. The legality test only uses
edges to assigned vertices, all of which lie in the ball. Replay the losing
queries above there. They remain in the ball, so this induced graph also loses
at clock n. The bounded radius need not give a finite ball. This paragraph
records the mathematical consequence of the lemmas below.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.LocalGame

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The vertices assigned a colour in a partial colouring. -/
def domain (f : V → Option Bool) : Set V := {x | f x ≠ none}

/-- A local response assigns new colours only at the query and its neighbours. -/
def IsLocal (f g : V → Option Bool) (x : V) : Prop :=
  domain g ⊆ domain f ∪ insert x (G.neighborSet x)

/-- A response may be chosen with both the size bound and the support bound. -/
theorem local_response_of_unfriendly {f p : V → Option Bool}
    (hf : HasFiniteDomain f) (hfp : Extends f p) (x : V) (hp : UnfriendlyAt G p x) :
    ∃ g, IsLegalResponse G f g x ∧ Extends g p ∧
      assignedCount g ≤ 2 * assignedCount f + 1 ∧ IsLocal G f g x := by
  classical
  obtain ⟨d, hd, hdp, hsize⟩ := bounded_response_of_unfriendly G hf hfp x hp
  let S := domain f ∪ insert x (G.neighborSet x)
  let g : V → Option Bool := fun y => if y ∈ S then d y else none
  have hgS (y : V) (hy : y ∈ S) : g y = d y := if_pos hy
  have hgdom : domain g ⊆ S := fun y hy => Classical.byContradiction fun h => hy (if_neg h)
  have hgsub : domain g ⊆ domain d := fun y hy h => hy ((hgS y (hgdom hy)).trans h)
  have hgfin : HasFiniteDomain g := hd.2.1.subset hgsub
  have hfg : Extends f g := fun y b hb =>
    (hgS y (Or.inl (fun h => Option.some_ne_none b (hb.symm.trans h)))).trans (hd.1 y b hb)
  have hgp : Extends g p := fun y b hb =>
    hdp y b ((hgS y (hgdom (fun h => Option.some_ne_none b (hb.symm.trans h)))).symm.trans hb)
  have hUF : UnfriendlyAt G g x := by
    obtain ⟨b, hdx, hc⟩ := hd.2.2
    have hn (c : Bool) : NeighColored G g x (some c) = NeighColored G d x (some c) :=
      congrArg (fun U : Set V => ↥U) (Set.ext fun y =>
        and_congr_right fun hy => Iff.of_eq
          (congrArg (fun e : Option Bool => e ∈ ({some c} : Set (Option Bool)))
            (hgS y (Or.inr (Or.inr hy)))))
    exact ⟨b, (hgS x (Or.inr (Or.inl rfl))).trans hdx, by rwa [hn, hn]⟩
  exact ⟨g, ⟨hfg, hgfin, hUF⟩, hgp, (Set.ncard_le_ncard hgsub hd.2.1).trans hsize, hgdom⟩

/-- The natural-clock game with bounded, local responses. -/
def LocalFiniteWins (f : V → Option Bool) : ℕ → Prop
  | 0 => True
  | n + 1 => ∀ x : V, ∃ g, IsLegalResponse G f g x ∧
      assignedCount g ≤ 2 * assignedCount f + 1 ∧ IsLocal G f g x ∧ LocalFiniteWins g n

private theorem wins_step (f : V → Option Bool) (n : ℕ) :
    PartitionerWins G f ((n + 1 : ℕ) : Ordinal.{v}) ↔
      ∀ x, ∃ g, IsLegalResponse G f g x ∧ PartitionerWins G g (n : Ordinal.{v}) := by
  rw [PartitionerWins]
  constructor
  · exact fun h x => h x _ (Nat.cast_lt.mpr (Nat.lt_succ_self n))
  · intro h x β hβ
    obtain ⟨g, hg, hw⟩ := h x
    rw [Nat.cast_add_one, ← Order.succ_eq_add_one] at hβ
    refine ⟨g, hg, ?_⟩
    rw [PartitionerWins] at hw ⊢
    exact fun y γ hγ => hw y γ (hγ.trans_le (Order.lt_succ_iff.mp hβ))

/-- Adding a support bound to the finite-clock game preserves its winning positions. -/
theorem partitionerWins_iff_localFiniteWins (f : V → Option Bool) (hf : HasFiniteDomain f) (n : ℕ) :
    PartitionerWins G f (n : Ordinal.{v}) ↔ LocalFiniteWins G f n := by
  induction n generalizing f
  case zero =>
    rw [PartitionerWins]
    simp [LocalFiniteWins]
  case succ n ih =>
    rw [wins_step, LocalFiniteWins]
    constructor
    · intro h x
      obtain ⟨p, hp, hwin⟩ := h x
      obtain ⟨g, hlegal, hgp, hsize, hlocal⟩ := local_response_of_unfriendly G hf hp.1 x hp.2.2
      exact ⟨g, hlegal, hsize, hlocal,
        (ih g hlegal.2.1).mp (partitionerWins_of_restriction G hgp hwin)⟩
    · intro h x
      obtain ⟨g, hlegal, _, _, hwin⟩ := h x
      exact ⟨g, hlegal, (ih g hlegal.2.1).mpr hwin⟩

/-- Two sets are farther apart than a given threshold in walk distance. -/
def Far (s : ℕ) (D E : Set V) : Prop :=
  ∀ x ∈ D, ∀ y ∈ E, ∀ w : G.Walk x y, s < w.length

/-- The separation needed to combine positions with the indicated clock. -/
def separation : ℕ → ℕ
  | 0 => 0
  | r + 1 => 2 * separation r + 2

/-- Combine two partial colourings whose assigned domains are disjoint. -/
def combine (f g : V → Option Bool) : V → Option Bool :=
  fun x => if f x = none then g x else f x

private def Near (s : ℕ) (D : Set V) (x : V) : Prop :=
  ∃ y ∈ D, ∃ p : G.Walk y x, p.length ≤ s

private theorem far_symm {s : ℕ} {D E : Set V} (h : Far G s D E) : Far G s E D :=
  fun x hx y hy p => by simpa only [SimpleGraph.Walk.length_reverse] using h y hy x hx p.reverse

private theorem walk_from_query {x y : V} (hy : y ∈ insert x (G.neighborSet x)) :
    ∃ w : G.Walk x y, w.length ≤ 1 := by
  rcases Set.mem_insert_iff.mp hy with rfl | h
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · exact ⟨(show G.Adj x y from h).toWalk, by simp⟩

private theorem far_expand {s : ℕ} {D E : Set V} {x : V} (h : Far G (2 * s + 2) D E)
    (hn : Near G (s + 1) D x) : Far G s (D ∪ insert x (G.neighborSet x)) E := by
  obtain ⟨a, ha, p, hp⟩ := hn
  rintro u (hu | hu) v hv w
  · exact (by omega : s ≤ 2 * s + 2).trans_lt (h u hu v hv w)
  · obtain ⟨q, hq⟩ := walk_from_query G hu
    have hlong := h a ha v hv ((p.append q).append w)
    simp only [SimpleGraph.Walk.length_append] at hlong
    omega

private theorem far_from_query {s : ℕ} {D : Set V} {x : V}
    (h : ¬ Near G (s + 1) D x) : Far G s (insert x (G.neighborSet x)) D := by
  intro y hy z hz w
  obtain ⟨p, hp⟩ := walk_from_query G hy
  by_contra hw
  refine h ⟨z, hz, (p.append w).reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_append]
  omega

private theorem no_adj_of_near_far {s : ℕ} {D E : Set V} {x : V}
    (h : Far G (2 * s + 2) D E) (hn : Near G (s + 1) D x) :
    ∀ y ∈ E, ¬ G.Adj x y := by
  intro y hy hadj
  obtain ⟨u, hu, p, hp⟩ := hn
  have hlong := h u hu y hy (p.append hadj.toWalk)
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk] at hlong
  omega

private theorem no_adj_of_not_near {s : ℕ} {D : Set V} {x : V}
    (h : ¬ Near G (s + 1) D x) : ∀ y ∈ D, ¬ G.Adj x y :=
  fun y hy ha => h ⟨y, hy, ha.symm.toWalk, by simp⟩

private theorem domain_combine (f g : V → Option Bool) :
    domain (combine f g) = domain f ∪ domain g := by
  ext x
  by_cases h : f x = none <;> simp [domain, combine, h]

private theorem far_no_common {s : ℕ} {D E : Set V} (h : Far G s D E)
    (x : V) (hxD : x ∈ D) (hxE : x ∈ E) : False :=
  (Nat.not_lt_zero s) (h x hxD x hxE SimpleGraph.Walk.nil)

private theorem combine_comm_of_far {s : ℕ} {f g : V → Option Bool}
    (hfar : Far G s (domain f) (domain g)) : combine f g = combine g f := by
  funext x
  by_cases hf : f x = none
  · by_cases hg : g x = none <;> simp [combine, hf, hg]
  · have hg : g x = none := Classical.byContradiction fun hn => far_no_common G hfar x hf hn
    simp [combine, hf, hg]

private theorem legal_combine_left {s : ℕ} {f f' g : V → Option Bool} {x : V}
    (hf : IsLegalResponse G f f' x) (hg : HasFiniteDomain g)
    (hfar : Far G s (domain f') (domain g)) (hno : ∀ y ∈ domain g, ¬ G.Adj x y) :
    IsLegalResponse G (combine f g) (combine f' g) x := by
  obtain ⟨hExt, hFin, b, hb, hcard⟩ := hf
  have hfinite : HasFiniteDomain (combine f' g) := by
    change (domain (combine f' g)).Finite
    rw [domain_combine]
    exact hFin.union hg
  have hleft : Extends f' (combine f' g) :=
    fun y c hc => (if_neg (fun h => Option.some_ne_none c (hc.symm.trans h))).trans hc
  refine ⟨?_, hfinite, b, hleft x b hb, ?_⟩
  · intro y c hc
    by_cases hy : f y = none
    · have hgy : g y = some c := (if_pos hy).symm.trans hc
      have hy' : f' y = none := Classical.byContradiction fun h =>
        far_no_common G hfar y h (fun hnone => Option.some_ne_none c (hgy.symm.trans hnone))
      exact (if_pos hy').trans hgy
    · exact hleft y c (hExt y c ((if_neg hy).symm.trans hc))
  · have hEq (y : V) (ha : G.Adj x y) : combine f' g y = f' y := by
      by_cases hy : f' y = none
      · have hgy : g y = none := Classical.byContradiction fun h => hno y h ha
        exact (if_pos hy).trans (hgy.trans hy.symm)
      · exact if_neg hy
    have hn (c : Bool) :
        NeighColored G (combine f' g) x (some c) = NeighColored G f' x (some c) :=
      congrArg (fun U : Set V => ↥U) (Set.ext fun y =>
        and_congr_right fun hy => Iff.of_eq
          (congrArg (fun e : Option Bool => e ∈ ({some c} : Set (Option Bool))) (hEq y hy)))
    rwa [hn, hn]

private theorem win_down {f : V → Option Bool} {α β : Ordinal.{v}}
    (h : PartitionerWins G f α) (hβα : β ≤ α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)

/-- Winning positions far enough apart can be combined at a finite clock,
provided the empty position also wins at that clock. -/
theorem wins_combine_of_far (n : ℕ) (f g : V → Option Bool)
    (hf : HasFiniteDomain f) (hg : HasFiniteDomain g)
    (he : PartitionerWins G (emptyPartition V) (n : Ordinal.{v}))
    (hfwin : PartitionerWins G f (n : Ordinal.{v}))
    (hgwin : PartitionerWins G g (n : Ordinal.{v}))
    (hfar : Far G (separation n) (domain f) (domain g)) :
    PartitionerWins G (combine f g) (n : Ordinal.{v}) := by
  induction n generalizing f g
  case zero => rw [PartitionerWins]; simp
  case succ n ih =>
    have hle : (n : Ordinal.{v}) ≤ ((n + 1 : ℕ) : Ordinal.{v}) := Nat.cast_le.mpr (Nat.le_succ n)
    have he' := win_down G he hle
    apply (wins_step G _ n).mpr
    intro x
    let s := separation n
    have hfar' : Far G (2 * s + 2) (domain f) (domain g) := hfar
    have serve (p q : V → Option Bool) (hp : HasFiniteDomain p) (hq : HasFiniteDomain q)
        (wp : PartitionerWins G p ((n + 1 : ℕ) : Ordinal.{v}))
        (wq : PartitionerWins G q ((n + 1 : ℕ) : Ordinal.{v}))
        (sep : Far G (2 * s + 2) (domain p) (domain q)) (hn : Near G (s + 1) (domain p) x) :
        ∃ h, IsLegalResponse G (combine p q) h x ∧ PartitionerWins G h (n : Ordinal.{v}) := by
      obtain ⟨d, hd, wd⟩ := (wins_step G p n).mp wp x
      obtain ⟨e, heL, hedge, _, hlocal⟩ := local_response_of_unfriendly G hp hd.1 x hd.2.2
      have hdist : Far G s (domain e) (domain q) :=
        fun u hu => far_expand G sep hn u (hlocal hu)
      exact ⟨combine e q, legal_combine_left G heL hq hdist (no_adj_of_near_far G sep hn),
        ih e q heL.2.1 hq he' (partitionerWins_of_restriction G hedge wd) (win_down G wq hle) hdist⟩
    by_cases hfn : Near G (s + 1) (domain f) x
    · exact serve f g hf hg hfwin hgwin hfar' hfn
    by_cases hgn : Near G (s + 1) (domain g) x
    · rw [combine_comm_of_far G hfar]
      exact serve g f hg hf hgwin hfwin (far_symm G hfar') hgn
    let old := combine f g
    have hfinOld : HasFiniteDomain old := by
      change (domain (combine f g)).Finite
      rw [domain_combine]
      exact hf.union hg
    have hsmall : Far G s (domain f) (domain g) :=
      fun u hu v hv w => (by omega : s ≤ 2 * s + 2).trans_lt (hfar' u hu v hv w)
    have hwinOld := ih f g hf hg he' (win_down G hfwin hle) (win_down G hgwin hle) hsmall
    have hnOld : ¬ Near G (s + 1) (domain old) x := by
      rintro ⟨y, hy, w, hw⟩
      change y ∈ domain (combine f g) at hy
      rw [domain_combine] at hy
      exact hy.elim (fun h => hfn ⟨y, h, w, hw⟩) (fun h => hgn ⟨y, h, w, hw⟩)
    obtain ⟨d, hd, wd⟩ := (wins_step G _ n).mp he x
    have hEmpty : HasFiniteDomain (emptyPartition V) := by simp [HasFiniteDomain, emptyPartition]
    obtain ⟨e, heL, hed, _, hlocal⟩ := local_response_of_unfriendly G hEmpty hd.1 x hd.2.2
    have hdist : Far G s (domain e) (domain old) :=
      fun u hu => far_from_query G hnOld u ((hlocal hu).resolve_left (fun h => h rfl))
    have hlegal := legal_combine_left G heL hfinOld hdist (no_adj_of_not_near G hnOld)
    have hOldEmpty : combine (emptyPartition V) old = combine f g := rfl
    exact ⟨combine e old, hOldEmpty ▸ hlegal,
      ih e old heL.2.1 hfinOld he' (partitionerWins_of_restriction G hed wd) hwinOld hdist⟩

/-- A first losing query for a position can be found near its assigned domain
when the empty position wins at the same clock. -/
theorem exists_near_losing_query {f : V → Option Bool} (hf : HasFiniteDomain f) (n : ℕ)
    (he : PartitionerWins G (emptyPartition V) ((n + 1 : ℕ) : Ordinal.{v}))
    (hprev : PartitionerWins G f (n : Ordinal.{v}))
    (hlose : ¬ PartitionerWins G f ((n + 1 : ℕ) : Ordinal.{v})) :
    ∃ x, (∃ y ∈ domain f, ∃ w : G.Walk y x, w.length ≤ separation n + 1) ∧
      ∀ g, IsLegalResponse G f g x → ¬ PartitionerWins G g (n : Ordinal.{v}) := by
  classical
  obtain ⟨x, hx⟩ := not_forall.mp ((wins_step G f n).not.mp hlose)
  refine ⟨x, ?_, fun g hg hw => hx ⟨g, hg, hw⟩⟩
  by_contra hfar
  obtain ⟨p, hp, hpwin⟩ := (wins_step G _ n).mp he x
  have hEmpty : HasFiniteDomain (emptyPartition V) := by simp [HasFiniteDomain, emptyPartition]
  obtain ⟨g, hg, hgp, _, hlocal⟩ := local_response_of_unfriendly G hEmpty hp.1 x hp.2.2
  have hdist : Far G (separation n) (domain g) (domain f) :=
    fun u hu => far_from_query G hfar u ((hlocal hu).resolve_left (fun h => h rfl))
  have hle : (n : Ordinal.{v}) ≤ ((n + 1 : ℕ) : Ordinal.{v}) := Nat.cast_le.mpr (Nat.le_succ n)
  have hlegal := legal_combine_left G hg hf hdist (no_adj_of_not_near G hfar)
  have hcombine : combine (emptyPartition V) f = f := rfl
  apply hx
  exact ⟨combine g f, hcombine ▸ hlegal,
    wins_combine_of_far G n g f hg.2.1 hf (win_down G he hle)
      (partitionerWins_of_restriction G hgp hpwin) hprev hdist⟩

end TenChallenges.Continuation.LocalGame

/- Inlined from Continuation/UnfriendlyInducedResponses.lean. -/
/-!
# Transferring responses from an induced graph

Extending a partial colouring by unassigned vertices preserves the coloured
neighbour sets, the number of assignments, and the support bound for a local
response.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.LocalGame

open scoped Cardinal

variable {V : Type u}

open Classical in
/-- Regard a partial colouring of an induced graph as a partial colouring of
the original graph. -/
noncomputable def liftInduced (B : Set V) (f : B → Option Bool) : V → Option Bool :=
  fun x => if hx : x ∈ B then f ⟨x, hx⟩ else none

@[simp] theorem liftInduced_eq (B : Set V) (f : B → Option Bool) (x : B) :
    liftInduced B f x.val = f x := by
  exact dif_pos x.property


@[simp] theorem liftInduced_empty (B : Set V) :
    liftInduced B (emptyPartition B) = emptyPartition V := by
  funext x
  by_cases hx : x ∈ B <;> simp [liftInduced, emptyPartition, hx]


theorem domain_liftInduced (B : Set V) (f : B → Option Bool) :
    domain (liftInduced B f) = Subtype.val '' domain f := by
  ext y
  by_cases hy : y ∈ B
  · let z : B := ⟨y, hy⟩
    change liftInduced B f z.val ≠ none ↔ z.val ∈ Subtype.val '' domain f
    rw [liftInduced_eq]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => Subtype.ext hwz ▸ hw⟩
  · constructor
    · intro h
      exact (h (dif_neg hy)).elim
    · rintro ⟨z, _, rfl⟩
      exact (hy z.property).elim


theorem domain_liftInduced_subset (B : Set V) (f : B → Option Bool) :
    domain (liftInduced B f) ⊆ B := by
  rw [domain_liftInduced]
  rintro _ ⟨x, _, rfl⟩
  exact x.property


theorem assignedCount_liftInduced (B : Set V) (f : B → Option Bool) :
    assignedCount (liftInduced B f) = assignedCount f := by
  change (domain (liftInduced B f)).ncard = (domain f).ncard
  rw [domain_liftInduced]
  exact Set.ncard_image_of_injective _ Subtype.val_injective


theorem hasFiniteDomain_liftInduced (B : Set V) (f : B → Option Bool) (h : HasFiniteDomain f) :
    HasFiniteDomain (liftInduced B f) := by
  change (domain (liftInduced B f)).Finite
  rw [domain_liftInduced]
  exact h.image Subtype.val


theorem local_legal_liftInduced (G : SimpleGraph V) (B : Set V)
    {f g : B → Option Bool} {x : B}
    (h : IsLegalResponse (G.induce B) f g x) (hl : IsLocal (G.induce B) f g x) :
    IsLegalResponse G (liftInduced B f) (liftInduced B g) x.val ∧
      IsLocal G (liftInduced B f) (liftInduced B g) x.val := by
  classical
  constructor
  · refine ⟨?_, hasFiniteDomain_liftInduced B g h.2.1, ?_⟩
    · intro y b hy
      have hyB : y ∈ B := domain_liftInduced_subset B f (show y ∈ domain (liftInduced B f) from
        fun hn => Option.some_ne_none b (hy.symm.trans hn))
      let z : B := ⟨y, hyB⟩
      have hz : f z = some b := (liftInduced_eq B f z).symm.trans hy
      exact (liftInduced_eq B g z).trans (h.1 z b hz)
    · obtain ⟨b, hgb, hcard⟩ := h.2.2
      refine ⟨b, (liftInduced_eq B g x).trans hgb, ?_⟩
      let e (t : Bool) : NeighColored (G.induce B) g x (some t) ≃
          NeighColored G (liftInduced B g) x.val (some t) :=
        { toFun := fun y => ⟨y.val.val, y.property.1,
            (liftInduced_eq B g y.val).trans y.property.2⟩
          invFun := fun y =>
            let z : B := ⟨y.val, domain_liftInduced_subset B g
              (show y.val ∈ domain (liftInduced B g) from
                fun hn => Option.some_ne_none t (y.property.2.symm.trans hn))⟩
            ⟨z, y.property.1, (liftInduced_eq B g z).symm.trans y.property.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Cardinal.mk_congr (e b)).symm.le.trans (hcard.trans (Cardinal.mk_congr (e (!b))).le)
  · unfold IsLocal
    rw [domain_liftInduced]
    rintro y ⟨z, hz, rfl⟩
    rcases hl hz with hf | he
    · apply Or.inl
      rw [domain_liftInduced]
      exact ⟨z, hf, rfl⟩
    · exact Or.inr (he.imp (congrArg Subtype.val) id)

end TenChallenges.Continuation.LocalGame

/- Inlined from Continuation/UnfriendlyLosingBall.lean. -/
/-!
# Induced balls witnessing a first finite loss

The least losing clock bounds how far a losing query must be from the
current assignments. Every new assignment lies at the query or an adjacent
vertex. A shrinking clock therefore supplies a distance budget for replaying
the loss in an induced ball.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.LosingBall

open LocalGame

variable {V : Type u} (G : SimpleGraph V)

/-- The vertices reachable from a root by a walk of length at most the radius. -/
def walkBall (root : V) (radius : ℕ) : Set V :=
  {x | ∃ w : G.Walk root x, w.length ≤ radius}

private theorem win_down {f : V → Option Bool} {α β : Ordinal.{v}}
    (h : PartitionerWins G f α) (hβα : β ≤ α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)

private theorem win_zero (f : V → Option Bool) : PartitionerWins G f (0 : Ordinal.{v}) := by
  rw [PartitionerWins]
  simp

private theorem wins_step (f : V → Option Bool) (n : ℕ) :
    PartitionerWins G f ((n + 1 : ℕ) : Ordinal.{v}) ↔
      ∀ x, ∃ g, IsLegalResponse G f g x ∧ PartitionerWins G g (n : Ordinal.{v}) := by
  rw [PartitionerWins]
  constructor
  · exact fun h x => h x _ (Nat.cast_lt.mpr (Nat.lt_succ_self n))
  · intro h x β hβ
    obtain ⟨g, hg, hw⟩ := h x
    rw [Nat.cast_add_one, ← Order.succ_eq_add_one] at hβ
    exact ⟨g, hg, win_down G hw (Order.lt_succ_iff.mp hβ)⟩

private theorem separation_formula (n : ℕ) : separation n = 2 ^ (n + 1) - 2 := by
  suffices h : ∀ m : ℕ, separation m + 2 = 2 ^ (m + 1) by
    exact Nat.eq_sub_of_add_eq (h n)
  intro m
  induction m
  case zero => rfl
  case succ m ih =>
    rw [separation, pow_succ]
    omega

private theorem separation_mono : Monotone separation := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [separation]
  omega

private theorem walkBall_mono (root : V) {r s : ℕ} (h : r ≤ s) :
    walkBall G root r ⊆ walkBall G root s := fun _ ⟨w, hw⟩ => ⟨w, hw.trans h⟩

private theorem local_support_ball {f g : V → Option Bool} {root query : V} {r s : ℕ}
    (hf : domain f ⊆ walkBall G root r) (hq : query ∈ walkBall G root (r + s + 1))
    (hloc : IsLocal G f g query) :
    domain g ⊆ walkBall G root (r + s + 2) := by
  intro y hy
  rcases hloc hy with hy | hy
  · exact walkBall_mono G root (by omega) (hf hy)
  · obtain ⟨w, hw⟩ := hq
    rcases Set.mem_insert_iff.mp hy with rfl | ha
    · exact ⟨w, by omega⟩
    · refine ⟨w.append (show G.Adj query y from ha).toWalk, ?_⟩
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk]
      omega

private theorem least_loss (f : V → Option Bool) (m : ℕ)
    (hloss : ¬ PartitionerWins G f (m : Ordinal.{v})) :
    ∃ k ≤ m, (∀ j < k, PartitionerWins G f (j : Ordinal.{v})) ∧
      ¬ PartitionerWins G f (k : Ordinal.{v}) := by
  classical
  have hex : ∃ k : ℕ, ¬ PartitionerWins G f (k : Ordinal.{v}) := ⟨m, hloss⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hloss,
    fun j hj => Classical.byContradiction (Nat.find_min hex hj), Nat.find_spec hex⟩

private theorem loses_in_arena (root : V) (B : Set V) (k : ℕ) (r : ℕ) (f : B → Option Bool)
    (hf : HasFiniteDomain f)
    (he : ∀ j ≤ k, PartitionerWins G (emptyPartition V) (j : Ordinal.{v}))
    (hprev : ∀ j < k, PartitionerWins G (liftInduced B f) (j : Ordinal.{v}))
    (hloss : ¬ PartitionerWins G (liftInduced B f) (k : Ordinal.{v}))
    (hr : domain (liftInduced B f) ⊆ walkBall G root r)
    (hB : walkBall G root (r + separation k) ⊆ B) :
    ¬ PartitionerWins (G.induce B) f (k : Ordinal.{v}) := by
  induction k using Nat.strong_induction_on generalizing r f
  rename_i k ih
  intro hArena
  cases k
  case zero => exact hloss (by simpa using win_zero G (liftInduced B f))
  case succ n =>
    have hfLift := hasFiniteDomain_liftInduced B f hf
    obtain ⟨query, ⟨y, hy, p, hp⟩, hbad⟩ :=
      exists_near_losing_query G hfLift n (he _ le_rfl) (hprev n (Nat.lt_succ_self n)) hloss
    obtain ⟨t, ht⟩ := hr hy
    have hq : query ∈ walkBall G root (r + separation n + 1) := by
      refine ⟨t.append p, ?_⟩
      rw [SimpleGraph.Walk.length_append]
      omega
    have hqIn : query ∈ B := hB ((walkBall_mono G root (show
        r + separation n + 1 ≤ r + separation (n + 1) by
      simp only [separation]
      omega)) hq)
    have hlocalArena := (partitionerWins_iff_localFiniteWins (G.induce B) f hf (n + 1)).mp hArena
    rw [LocalFiniteWins] at hlocalArena
    obtain ⟨g, hg, _, hgLocal, hgCont⟩ := hlocalArena ⟨query, hqIn⟩
    obtain ⟨hlegal, hlocal⟩ := local_legal_liftInduced G B hg hgLocal
    have hlossG := hbad (liftInduced B g) hlegal
    obtain ⟨k, hk, hkBefore, hkLoss⟩ := least_loss G (liftInduced B g) n hlossG
    have hr' := local_support_ball G hr hq hlocal
    have hB' : walkBall G root ((r + separation n + 2) + separation k) ⊆ B := by
      refine (walkBall_mono G root ?_).trans hB
      have hm := separation_mono hk
      simp only [separation]
      omega
    have hwCont := (partitionerWins_iff_localFiniteWins (G.induce B) g hg.2.1 n).mpr hgCont
    apply ih k (Nat.lt_succ_of_le hk) (r + separation n + 2) g hg.2.1
      (fun j hj => he j (hj.trans (Nat.le_succ_of_le hk))) hkBefore hkLoss hr' hB'
    exact win_down (G.induce B) hwCont (Nat.cast_le.mpr hk)

/-- If the empty position first loses at natural clock n, an induced ball of
radius 2^n - 2 already loses at that clock. -/
theorem exists_induced_losing_ball (n : ℕ)
    (hprev : ∀ m < n, PartitionerWins G (emptyPartition V) (m : Ordinal.{v}))
    (hloss : ¬ PartitionerWins G (emptyPartition V) (n : Ordinal.{v})) :
    ∃ root : V,
      ¬ PartitionerWins (G.induce (walkBall G root (2 ^ n - 2)))
        (emptyPartition (walkBall G root (2 ^ n - 2))) (n : Ordinal.{v}) := by
  classical
  cases n
  case zero => exact (hloss (by simpa using win_zero G (emptyPartition V))).elim
  case succ n =>
    obtain ⟨a, ha⟩ := not_forall.mp ((wins_step G (emptyPartition V) n).not.mp hloss)
    let B := walkBall G a (2 ^ (n + 1) - 2)
    have haB : a ∈ B := ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
    refine ⟨a, ?_⟩
    intro hwin
    have hEmpty : HasFiniteDomain (emptyPartition B) := by simp [HasFiniteDomain, emptyPartition]
    have hlocal := (partitionerWins_iff_localFiniteWins (G.induce B) (emptyPartition B) hEmpty (n + 1)).mp hwin
    rw [LocalFiniteWins] at hlocal
    obtain ⟨g, hg, hsize, hl, hcont⟩ := hlocal ⟨a, haB⟩
    have hlegal := (local_legal_liftInduced G B hg hl).1
    have hgloss : ¬ PartitionerWins G (liftInduced B g) (n : Ordinal.{v}) :=
      fun hw => ha ⟨liftInduced B g, liftInduced_empty B ▸ hlegal, hw⟩
    have hsmall : assignedCount (liftInduced B g) ≤ 1 := by
      rw [assignedCount_liftInduced]
      simpa [assignedCount, emptyPartition] using hsize
    have : Finite (domain (liftInduced B g)) :=
      (show (domain (liftInduced B g)).Finite from hlegal.2.1).to_subtype
    have hsingle : (domain (liftInduced B g)).Subsingleton :=
      Set.ncard_le_one_iff_subsingleton.mp hsmall
    obtain ⟨b, hb, _⟩ := hlegal.2.2
    have haD : a ∈ domain (liftInduced B g) := fun h => Option.some_ne_none b (hb.symm.trans h)
    have hsupp : domain (liftInduced B g) ⊆ walkBall G a 0 := fun x hx =>
      (hsingle haD hx) ▸ (show a ∈ walkBall G a 0 from ⟨SimpleGraph.Walk.nil, Nat.le_refl _⟩)
    obtain ⟨k, hk, hbefore, hbad⟩ := least_loss G (liftInduced B g) n hgloss
    have hB : walkBall G a (0 + separation k) ⊆ B := by
      apply walkBall_mono G a
      rw [zero_add, ← separation_formula n]
      exact separation_mono hk
    have hcont' := (partitionerWins_iff_localFiniteWins (G.induce B) g hg.2.1 n).mpr hcont
    apply loses_in_arena G a B k 0 g hg.2.1 (fun j hj => hprev j (Nat.lt_succ_of_le (hj.trans hk)))
      hbefore hbad hsupp hB
    exact win_down (G.induce B) hcont' (Nat.cast_le.mpr hk)

end TenChallenges.Continuation.LosingBall

theorem solution {V : Type u} (G : SimpleGraph V) (n : ℕ)
    (hprev : ∀ m : ℕ, m < n → PartitionerWins G (emptyPartition V) (m : Ordinal.{v}))
    (hloss : ¬ PartitionerWins G (emptyPartition V) (n : Ordinal.{v})) :
    ∃ a : V,
      let B : Set V := {x | ∃ w : G.Walk a x, w.length ≤ 2 ^ n - 2}
      ¬ PartitionerWins (G.induce B) (emptyPartition B) (n : Ordinal.{v}) := by
  exact TenChallenges.Continuation.LosingBall.exists_induced_losing_ball G n hprev hloss

#print axioms solution
