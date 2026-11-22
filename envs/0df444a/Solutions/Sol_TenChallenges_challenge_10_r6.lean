-- Prove2me | solution 1 for TenChallenges.challenge_10_r6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T11:24:11.792317+00:00
-- url     : https://prove2.me/submissions/a17e5bb8-aa72-4120-9d74-b1eb0b2184d0

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
set_option linter.all false

namespace R6TableCheck

private def decideRows : (n : Nat) → (P : (Fin n → Bool) → Prop) →
    [DecidablePred P] → Decidable (∀ r, P r)
  | 0, P, _ => decidable_of_iff (P (fun i => i.elim0))
      ⟨fun h r => (Subsingleton.elim (fun i : Fin 0 => (i.elim0 : Bool)) r) ▸ h,
        fun h => h _⟩
  | n+1, P, _ =>
    letI (b : Bool) : Decidable (∀ r : Fin n → Bool, P (Fin.cons b r)) :=
      decideRows n (fun r => P (Fin.cons b r))
    decidable_of_iff' (∀ (b : Bool) (r : Fin n → Bool), P (Fin.cons b r)) Fin.forall_fin_succ_pi

instance (priority := 2000) (n : Nat) (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    Decidable (∀ r, P r) := decideRows n P

end R6TableCheck

-- Source: Continuation/Challenge10Next.lean
section

set_option linter.all false

universe u v

namespace Continuation.TC10
open Classical SimpleGraph
open scoped Cardinal
variable {V : Type u} (G : SimpleGraph V)

/-- Every colored vertex is currently unfriendly. -/
def Stable (f : V → Option Bool) : Prop :=
  ∀ x b, f x = some b → UnfriendlyAt G f x

/-- Two simple shapes of a partial coloring which can safely accommodate one more query. -/
def Ready (f : V → Option Bool) : Prop :=
  ((∀ x b, f x = some b → b = false) ∧
    ∀ x y, f x = some false → f y = some false → ¬ G.Adj x y) ∨
  ((∀ b, (f ⁻¹' {some b}).Subsingleton) ∧
    ∀ x b, f x = some b → ∃ y, G.Adj x y ∧ f y = some (!b))

lemma neigh_update {f : V → Option Bool} (x : V) (b c : Bool) :
    #(NeighColored G (Function.update f x (some b)) x (some c)) =
      #(NeighColored G f x (some c)) := by
  apply Cardinal.mk_congr
  exact Equiv.subtypeEquivRight fun y => and_congr_right fun hy => by
    simp only [Set.mem_preimage, Function.update_of_ne (G.ne_of_adj hy).symm]

lemma no_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b) (hno : ∀ y, G.Adj x y → f y ≠ some b) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, ?_⟩
  have hempty : IsEmpty (NeighColored G f x (some b)) :=
    ⟨fun ⟨y, hy⟩ => hno y hy.1 hy.2⟩
  exact (@Cardinal.mk_eq_zero (NeighColored G f x (some b)) hempty).symm ▸ zero_le

lemma unique_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b)
    (hsame : (G.neighborSet x ∩ f ⁻¹' {some b}).Subsingleton)
    (hopp : ∃ y, G.Adj x y ∧ f y = some (!b)) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, hsame.cardinalMk_le_one.trans ?_⟩
  exact Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr
    (let ⟨y, hya, hyc⟩ := hopp; ⟨⟨y, hya, hyc⟩⟩))

lemma minority_update (f : V → Option Bool) (x : V) :
    ∃ b, UnfriendlyAt G (Function.update f x (some b)) x := by
  rcases le_total #(NeighColored G f x (some false)) #(NeighColored G f x (some true)) with h | h
  · exact ⟨false, false, by simp, by simpa only [neigh_update, Bool.not_false] using h⟩
  · exact ⟨true, true, by simp, by simpa only [neigh_update, Bool.not_true] using h⟩

lemma update_extends {f : V → Option Bool} {x : V} (hx : f x = none) (b : Bool) :
    Extends f (Function.update f x (some b)) := by
  intro y c hfy
  have hyx : y ≠ x := fun heq => by simpa [heq, hx] using hfy
  simpa only [Function.update_of_ne hyx] using hfy

lemma finite_update {f : V → Option Bool} (hf : HasFiniteDomain f) (x : V) (b : Bool) :
    HasFiniteDomain (Function.update f x (some b)) := by
  exact (hf.insert x).subset (fun y hy => (eq_or_ne y x).elim
    (fun h => Or.inl h)
    (fun h => Or.inr (by simpa only [Set.mem_setOf_eq, Function.update_of_ne h] using hy)))

lemma wins_zero (f : V → Option Bool) : PartitionerWins G f (0 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun _ _ h => (not_lt_zero h).elim


lemma stable_wins_one {f : V → Option Bool} (hf : HasFiniteDomain f) (hs : Stable G f) :
    PartitionerWins G f (1 : Ordinal.{v}) := by
  classical
  rw [PartitionerWins]
  intro x β hβ
  obtain rfl := Order.lt_one_iff.mp hβ
  exact (Classical.em (f x = none)).elim
    (fun hx => let ⟨b, hb⟩ := minority_update G f x
      ⟨Function.update f x (some b),
        ⟨update_extends hx b, finite_update hf x b, hb⟩, wins_zero G _⟩)
    (fun hx => let ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
      ⟨f, ⟨fun _ _ h => h, hf, hs x b hb⟩, wins_zero G _⟩)

lemma ready_stable {f : V → Option Bool} (hr : Ready G f) : Stable G f := by
  intro x b hfx
  rcases hr with ⟨hc, hi⟩ | ⟨hs, ho⟩
  · exact no_same G b hfx (fun y hxy hfy =>
      hi x y (hc x b hfx ▸ hfx) (hc y b hfy ▸ hfy) hxy)
  · exact no_same G b hfx (fun y hxy hfy => G.ne_of_adj hxy (hs b hfx hfy))

lemma ready_update {f : V → Option Bool} (hr : Ready G f) {x : V}
    (hx : f x = none) : ∃ b, Stable G (Function.update f x (some b)) := by
  rcases hr with hind | hsparse
  · refine ⟨true, fun y c hy => no_same G c hy ?_⟩
    intro z hyz hz
    cases c
    · simp [Function.update_apply, ite_eq_iff] at hy hz
      exact hind.2 y z hy.2 hz.2 hyz
    · have htrue : ∀ w, f w ≠ some true := fun w hw => Bool.noConfusion (hind.1 w true hw)
      simp [Function.update_apply, ite_eq_iff, htrue] at hy hz
      exact G.ne_of_adj hyz (hy.trans hz.symm)
  · obtain ⟨b, hb⟩ := minority_update G f x
    refine ⟨b, fun y c hy => ?_⟩
    by_cases hyx : y = x
    · exact hyx.symm ▸ hb
    · refine unique_same G c hy ?_ ?_
      · refine (Set.subsingleton_singleton (a := x)).anti ?_
        intro z hz
        by_contra hzx
        exact G.ne_of_adj hz.1 (hsparse.1 c
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hyx] using hy)
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hzx] using hz.2))
      · obtain ⟨z, hzy, hz⟩ := hsparse.2 y c (by simpa only [Function.update_of_ne hyx] using hy)
        exact ⟨z, hzy, update_extends hx b z (!c) hz⟩

lemma ready_response {f : V → Option Bool} (hf : HasFiniteDomain f) (hr : Ready G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Stable G g := by
  by_cases hx : f x = none
  · obtain ⟨b, hb⟩ := ready_update G hr hx
    exact ⟨_, ⟨update_extends hx b, finite_update hf x b, hb x b (by simp)⟩, hb⟩
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨f, ⟨fun _ _ h => h, hf, ready_stable G hr x b hb⟩, ready_stable G hr⟩

noncomputable def first (a : V) : V → Option Bool :=
  Function.update (emptyPartition V) a (some false)

noncomputable def second (a b : V) : V → Option Bool :=
  Function.update (first a) b (some (if G.Adj a b then true else false))

lemma first_legal (a : V) : IsLegalResponse G (emptyPartition V) (first a) a := by
  refine ⟨update_extends rfl false,
    finite_update (by simp [HasFiniteDomain, emptyPartition]) a false,
    no_same G false (by simp [first]) ?_⟩
  intro y hay
  simp [first, Function.update_of_ne (G.ne_of_adj hay).symm, emptyPartition]

lemma second_legal_ready (a b : V) :
    IsLegalResponse G (first a) (second G a b) b ∧ Ready G (second G a b) := by
  have hr : Ready G (second G a b) := by
    by_cases hab : G.Adj a b
    · have hne := G.ne_of_adj hab
      have hfalse (x : V) : second G a b x = some false ↔ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
        exact fun e => e.symm ▸ hne
      have htrue (x : V) : second G a b x = some true ↔ x = b := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
      refine Or.inr ⟨?_, ?_⟩
      · intro c
        cases c
        · exact fun x hx y hy => (hfalse x).mp hx |>.trans ((hfalse y).mp hy).symm
        · exact fun x hx y hy => (htrue x).mp hx |>.trans ((htrue y).mp hy).symm
      · rintro x (_ | _) hx
        · exact ⟨b, ((hfalse x).mp hx).symm ▸ hab, (htrue b).mpr rfl⟩
        · exact ⟨a, ((htrue x).mp hx).symm ▸ hab.symm, (hfalse a).mpr rfl⟩
    · have hfalse (x : V) : second G a b x = some false ↔ x = b ∨ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition, imp_iff_not_or]
      refine Or.inl ⟨?_, ?_⟩
      · rintro x (_ | _) hx
        · rfl
        · simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition] at hx
      · intro x y hx hy
        rcases (hfalse x).mp hx with rfl | rfl
        all_goals rcases (hfalse y).mp hy with rfl | rfl
        all_goals simp_all [SimpleGraph.adj_comm]
  refine ⟨⟨?_, finite_update (first_legal G a).2.1 b (if G.Adj a b then true else false),
    ready_stable G hr b (if G.Adj a b then true else false) (by simp [second])⟩, hr⟩
  intro x c hx
  simp [first, Function.update_apply, emptyPartition, ite_eq_iff] at hx
  rcases hx with ⟨rfl, rfl⟩
  by_cases hxb : x = b <;> simp [second, first, hxb]


lemma wins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)


/-- Partitioner wins the four-round game on every simple graph, without a countability assumption. -/
theorem win_four : PartitionerWins G (emptyPartition V) (4 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro a α hα
  refine ⟨first a, first_legal G a,
    wins_mono G (Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => α < o) (Ordinal.natCast_succ 3)).mp hα)) ?_⟩
  rw [PartitionerWins]
  intro b β hβ
  refine ⟨second G a b, (second_legal_ready G a b).1,
    wins_mono G (Order.lt_succ_iff.mp
      ((congrArg (fun o : Ordinal.{v} => β < o) (Ordinal.natCast_succ 2)).mp hβ)) ?_⟩
  rw [PartitionerWins]
  intro c γ hγ
  obtain ⟨g, hg, hs⟩ := ready_response G (second_legal_ready G a b).1.2.1
    (second_legal_ready G a b).2 c
  exact ⟨g, hg, wins_mono G
    ((show ((1 : ℕ) : Ordinal.{v}) = 1 from Nat.cast_one) ▸ Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => γ < o)
      (Ordinal.natCast_succ 1)).mp hγ)) (stable_wins_one G hg.2.1 hs)⟩

end Continuation.TC10

end

-- Source: Continuation/UnfriendlyMonotone.lean
section

open scoped Cardinal

namespace Continuation.TC10R5Helpers

universe u

/-- An extension preserves unfriendliness if it adds no neighbors of the vertex's own color. -/
theorem unfriendly_of_extends_no_new_same {V : Type u} (G : SimpleGraph V)
    {f g : V → Option Bool} {v : V} {b : Bool}
    (hfg : Extends f g) (hfv : f v = some b) (hu : UnfriendlyAt G f v)
    (hsame : ∀ w, G.Adj v w → g w = some b → f w = some b) :
    UnfriendlyAt G g v := by
  rcases hu with ⟨c, hfc, hcard⟩
  obtain rfl : c = b := Option.some.inj (hfc.symm.trans hfv)
  have hsame_subset : G.neighborSet v ∩ g ⁻¹' {some c} ⊆
      G.neighborSet v ∩ f ⁻¹' {some c} := fun w hw => ⟨hw.1, hsame w hw.1 hw.2⟩
  have hopp_subset : G.neighborSet v ∩ f ⁻¹' {some (!c)} ⊆
      G.neighborSet v ∩ g ⁻¹' {some (!c)} := fun w hw => ⟨hw.1, hfg w (!c) hw.2⟩
  exact ⟨c, hfg v c hfv, (Cardinal.mk_le_mk_of_subset hsame_subset).trans
    (hcard.trans (Cardinal.mk_le_mk_of_subset hopp_subset))⟩

open Classical in
/-- Adding an opposite-colored or nonadjacent vertex preserves unfriendliness. -/
theorem unfriendly_update_of_color_or_nonadj {V : Type u} (G : SimpleGraph V)
    {f : V → Option Bool} {x y : V} {c d : Bool}
    (hx : f x = none) (hfy : f y = some c) (hu : UnfriendlyAt G f y)
    (hkeep : d ≠ c ∨ ¬ G.Adj y x) :
    UnfriendlyAt G (Function.update f x (some d)) y := by
  refine unfriendly_of_extends_no_new_same G ?_ hfy hu ?_
  · intro z e hz
    have hzx : z ≠ x := fun h => by simp [h, hx] at hz
    simpa only [Function.update_of_ne hzx] using hz
  · intro w hadj hgw
    have hwx : w ≠ x := fun e => hkeep.elim
      (fun hne => hne (Option.some.inj (by simpa only [e, Function.update_self] using hgw)))
      (fun hna => hna (e ▸ hadj))
    simpa only [Function.update_of_ne hwx] using hgw

end Continuation.TC10R5Helpers

end

-- Source: Continuation/Challenge10R5Support.lean
section

set_option linter.all false

universe u v

namespace Continuation.TC10R5

open Classical SimpleGraph
open scoped Cardinal
open TC10

variable {V : Type u} (G : SimpleGraph V)

/-- A stable coloring with at most one exceptional-colored vertex, which has an opposite neighbor. -/
def Safe (f : V → Option Bool) : Prop :=
  Stable G f ∧ ∃ b : Bool, (f ⁻¹' {some (!b)}).Subsingleton ∧
    ∀ y, f y = some (!b) → ∃ z, G.Adj y z ∧ f z = some b

lemma exceptional_update {f : V → Option Bool} {x : V} (hx : f x = none) (b d : Bool)
    (hsingle : (f ⁻¹' {some (!b)}).Subsingleton)
    (hopp : ∀ y, f y = some (!b) → ∃ z, G.Adj y z ∧ f z = some b)
    {y : V} (hy : f y = some (!b)) :
    UnfriendlyAt G (Function.update f x (some d)) y := by
  refine unique_same G (!b) (update_extends hx d y (!b) hy) ?_ ?_
  · refine (Set.subsingleton_singleton (a := x)).anti ?_
    intro z hz
    by_contra hzx
    exact G.ne_of_adj hz.1 (hsingle hy (by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff,
        Function.update_of_ne hzx] using hz.2))
  · obtain ⟨z, hyz, hz⟩ := hopp y hy
    exact ⟨z, hyz, by simpa only [Bool.not_not] using update_extends hx d z b hz⟩

lemma stable_update_exceptional {f : V → Option Bool} {x : V} (hx : f x = none)
    (hstable : Stable G f) (b d : Bool)
    (hsingle : (f ⁻¹' {some (!b)}).Subsingleton)
    (hopp : ∀ y, f y = some (!b) → ∃ z, G.Adj y z ∧ f z = some b)
    (hnew : UnfriendlyAt G (Function.update f x (some d)) x)
    (hkeep : ∀ y, f y = some b → d ≠ b ∨ ¬ G.Adj y x) :
    Stable G (Function.update f x (some d)) := by
  intro y c hy
  by_cases hyx : y = x
  · exact hyx.symm ▸ hnew
  · have hyold : f y = some c := by
      simpa only [Function.update_of_ne hyx] using hy
    rcases Bool.eq_or_eq_not c b with rfl | rfl
    · exact TC10R5Helpers.unfriendly_update_of_color_or_nonadj G hx hyold
        (hstable y c hyold) (hkeep y hyold)
    · exact exceptional_update G hx b d hsingle hopp hyold

lemma safe_update {f : V → Option Bool} (hs : Safe G f) {x : V} (hx : f x = none) :
    ∃ d, Stable G (Function.update f x (some d)) := by
  rcases hs with ⟨hstable, b, hsingle, hopp⟩
  by_cases hnb : ∃ y, G.Adj x y ∧ f y = some b
  · obtain ⟨y, hxy, hfy⟩ := hnb
    exact ⟨!b, stable_update_exceptional G hx hstable b (!b) hsingle hopp
      (unique_same G (!b) (by simp)
        (hsingle.anti (fun z hz => by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff,
            Function.update_of_ne (G.ne_of_adj hz.1).symm] using hz.2))
        ⟨y, hxy, by simpa only [Bool.not_not,
          Function.update_of_ne (G.ne_of_adj hxy).symm] using hfy⟩)
      (fun _ _ => Or.inl (Bool.not_ne_self b))⟩
  · exact ⟨b, stable_update_exceptional G hx hstable b b hsingle hopp
      (no_same G b (by simp) (fun y hxy hy => hnb
        ⟨y, hxy, by simpa only [Function.update_of_ne (G.ne_of_adj hxy).symm] using hy⟩))
      (fun y hy => Or.inr (fun hyx => hnb ⟨y, hyx.symm, hy⟩))⟩

lemma safe_response {f : V → Option Bool} (hf : HasFiniteDomain f)
    (hs : Safe G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Stable G g := by
  exact (Classical.em (f x = none)).elim
    (fun hx => let ⟨d, hd⟩ := safe_update G hs hx
      ⟨_, ⟨update_extends hx d, finite_update hf x d, hd x d (by simp)⟩, hd⟩)
    (fun hx => let ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
      ⟨f, ⟨fun _ _ h => h, hf, hs.1 x b hb⟩, hs.1⟩)

end Continuation.TC10R5

end

-- Source: Continuation/Challenge10R5.lean
section

set_option linter.all false

universe u v
namespace Continuation.TC10R5

open Classical SimpleGraph TC10
open scoped Cardinal
variable {V : Type u} (G : SimpleGraph V)

lemma independent_safe {f : V → Option Bool}
    (hc : ∀ x b, f x = some b → b = false)
    (hi : ∀ x y, f x = some false → f y = some false → ¬ G.Adj x y) : Safe G f := by
  exact ⟨ready_stable G (Or.inl ⟨hc, hi⟩), false,
    (fun y hy _ _ => False.elim (Bool.noConfusion (hc y true hy))),
    (fun y hy => False.elim (Bool.noConfusion (hc y true hy)))⟩

lemma ready_safe_update {f : V → Option Bool} (hr : Ready G f) {x : V} (hx : f x = none) :
    ∃ d, Safe G (Function.update f x (some d)) := by
  rcases hr with hind | hsparse
  · by_cases hn : ∃ y, G.Adj x y ∧ f y = some false
    · have htrue : ∀ y, f y ≠ some true :=
        fun y hy => Bool.noConfusion (hind.1 y true hy)
      have hnew (y : V) : Function.update f x (some true) y = some true ↔ y = x := by
        simp [Function.update_apply, ite_eq_iff, htrue]
      refine ⟨true, ?_, false, ?_, ?_⟩
      · refine fun y c hy => no_same G c hy ?_
        intro z hyz hz
        cases c
        · simp [Function.update_apply, ite_eq_iff] at hy hz
          exact hind.2 y z hy.2 hz.2 hyz
        · exact G.ne_of_adj hyz (((hnew y).mp hy).trans ((hnew z).mp hz).symm)
      · exact fun y hy z hz => ((hnew y).mp hy).trans ((hnew z).mp hz).symm
      · exact fun y hy => let ⟨z, hxz, hz⟩ := hn
          ⟨z, ((hnew y).mp hy).symm ▸ hxz, update_extends hx true z false hz⟩
    · refine ⟨false, independent_safe G ?_ ?_⟩
      · exact fun y c hy => (eq_or_ne y x).elim
          (fun hyx => Option.some.inj (by simpa [hyx] using hy.symm))
          (fun hyx => hind.1 y c (by simpa only [Function.update_of_ne hyx] using hy))
      · intro y z hy hz hyz
        by_cases hyx : y = x
        · exact hn ⟨z, hyx ▸ hyz, by
            simpa only [Function.update_of_ne (hyx ▸ (G.ne_of_adj hyz).symm)] using hz⟩
        · by_cases hzx : z = x
          · exact hn ⟨y, hzx ▸ hyz.symm, by
              simpa only [Function.update_of_ne hyx] using hy⟩
          · exact hind.2 y z
              (by simpa only [Function.update_of_ne hyx] using hy)
              (by simpa only [Function.update_of_ne hzx] using hz) hyz
  · obtain ⟨d, hd⟩ := ready_update G (Or.inr hsparse) hx
    have hold (y : V) (hy : Function.update f x (some d) y = some (!d)) :
        f y = some (!d) := by
      by_cases hyx : y = x
      · simp [hyx] at hy
      · simpa only [Function.update_of_ne hyx] using hy
    refine ⟨d, hd, d, ?_, ?_⟩
    · exact fun y hy z hz => hsparse.1 (!d) (hold y hy) (hold z hz)
    · exact fun y hy => let ⟨z, hyz, hz⟩ := hsparse.2 y (!d) (hold y hy)
        ⟨z, hyz, update_extends hx d z d (by simpa only [Bool.not_not] using hz)⟩

lemma ready_safe {f : V → Option Bool} (hr : Ready G f) : Safe G f := by
  exact hr.elim (fun h => independent_safe G h.1 h.2)
    (fun h => ⟨ready_stable G (Or.inr h), false, h.1 true,
      fun y hy => by simpa only [Bool.not_true] using h.2 y true hy⟩)

lemma ready_safe_response {f : V → Option Bool} (hf : HasFiniteDomain f)
    (hr : Ready G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Safe G g := by
  exact (Classical.em (f x = none)).elim
    (fun hx => let ⟨d, hd⟩ := ready_safe_update G hr hx
      ⟨Function.update f x (some d),
        ⟨update_extends hx d, finite_update hf x d, hd.1 x d (by simp)⟩, hd⟩)
    (fun hx => let ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
      ⟨f, ⟨fun _ _ h => h, hf, ready_stable G hr x d hd⟩, ready_safe G hr⟩)

lemma safe_wins_two {f : V → Option Bool} (hf : HasFiniteDomain f) (hs : Safe G f) :
    PartitionerWins G f (2 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun x β hβ => let ⟨g, hg, hstable⟩ := safe_response G hf hs x
    ⟨g, hg, wins_mono G
      ((show ((1 : ℕ) : Ordinal.{v}) = 1 from Nat.cast_one) ▸
        Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => β < o)
          (Ordinal.natCast_succ 1)).mp hβ))
      (stable_wins_one G hg.2.1 hstable)⟩

lemma ready_wins_three {f : V → Option Bool} (hf : HasFiniteDomain f) (hr : Ready G f) :
    PartitionerWins G f (3 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun x β hβ => let ⟨g, hg, hs⟩ := ready_safe_response G hf hr x
    ⟨g, hg, wins_mono G
      (Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => β < o)
        (Ordinal.natCast_succ 2)).mp hβ)) (safe_wins_two G hg.2.1 hs)⟩

/-- Partitioner wins the five-round game on every simple graph. -/
theorem win_five : PartitionerWins G (emptyPartition V) (5 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro a α hα
  refine ⟨first a, first_legal G a,
    wins_mono G (Order.lt_succ_iff.mp
      ((congrArg (fun o : Ordinal.{v} => α < o) (Ordinal.natCast_succ 4)).mp hα)) ?_⟩
  rw [PartitionerWins]
  intro b β hβ
  exact ⟨second G a b, (second_legal_ready G a b).1,
    wins_mono G (Order.lt_succ_iff.mp
      ((congrArg (fun o : Ordinal.{v} => β < o) (Ordinal.natCast_succ 3)).mp hβ))
      (ready_wins_three G (second_legal_ready G a b).1.2.1 (second_legal_ready G a b).2)⟩

end Continuation.TC10R5

end

-- Source: Continuation/UnfriendlyFromGlobal.lean
section

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- An extension unfriendly at the queried vertex admits a finite consistent response. -/
theorem finite_response_of_unfriendly_partition (p : V → Option Bool)
    (f : V → Option Bool) (hf : HasFiniteDomain f) (hfp : Extends f p)
    (v : V) (hp : UnfriendlyAt G p v) :
    ∃ g, IsLegalResponse G f g v ∧ Extends g p := by
  classical
  obtain ⟨b, hpv, hcard⟩ := hp
  let S : Set V := G.neighborSet v ∩ f ⁻¹' {some b}
  have hS : S.Finite := hf.subset
    (fun _ hx => Option.ne_none_iff_exists'.mpr ⟨b, hx.2⟩)
  have hsub : S ⊆ G.neighborSet v ∩ p ⁻¹' {some b} :=
    fun x hx => ⟨hx.1, hfp x b hx.2⟩
  obtain ⟨e⟩ := (Cardinal.le_def S (NeighColored G p v (some (!b)))).mp
    ((Cardinal.mk_le_mk_of_subset hsub).trans hcard)
  letI : Finite S := hS.to_subtype
  let T : Set V := Set.range fun x : S => (e x).1
  have hT : T.Finite := Set.finite_range _
  have hTc : ∀ x ∈ T, p x = some (!b) :=
    fun _ ⟨y, hy⟩ => hy ▸ (e y).2.2
  let g : V → Option Bool := fun x => if x = v ∨ x ∈ T then p x else f x
  have hfg : Extends f g := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).trans (hfp x c hc)
    else (if_neg h).trans hc
  have hgp : Extends g p := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).symm.trans hc
    else hfp x c ((if_neg h).symm.trans hc)
  have hgf : HasFiniteDomain g := (hf.union ((Set.finite_singleton v).union hT)).subset
    fun x hx => if h : x = v ∨ x ∈ T then Or.inr h else Or.inl
      (fun hn => hx ((if_neg h).trans hn))
  have hsame : (G.neighborSet v ∩ g ⁻¹' {some b}) ⊆ S := fun x hx =>
    ⟨hx.1, if h : x = v ∨ x ∈ T then h.elim
      (fun hv => False.elim (G.irrefl (hv ▸ hx.1)))
      (fun ht => False.elim ((Bool.not_eq_self b).mp (Option.some.inj
        ((hTc x ht).symm.trans ((if_pos h).symm.trans hx.2)))))
    else (if_neg h).symm.trans hx.2⟩
  let E : S ↪ NeighColored G g v (some (!b)) :=
    ⟨fun s => ⟨(e s).1, (e s).2.1,
      (if_pos (Or.inr ⟨s, rfl⟩)).trans (e s).2.2⟩,
      fun s t h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g v (some (!b)) => z.val) h))⟩
  exact ⟨g, ⟨hfg, hgf, b, (if_pos (Or.inl rfl)).trans hpv,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩, hgp⟩

/-- Finite partial partitions consistent with a global unfriendly partition
win at every clock. -/
theorem wins_from_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) :
    ∀ (α : Ordinal.{v}) (f : V → Option Bool),
      HasFiniteDomain f → Extends f p → PartitionerWins G f α := by
  intro α
  induction α using WellFoundedLT.induction
  rename_i α ih
  intro f hf hfp
  rw [PartitionerWins]
  exact fun x β hβ =>
    let ⟨g, hg, hgp⟩ := finite_response_of_unfriendly_partition G p f hf hfp x (hp x)
    ⟨g, hg, ih β hβ g hg.2.1 hgp⟩

/-- A global unfriendly partition gives Partitioner a winning strategy at every ordinal clock. -/
theorem partitionerWins_of_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α := by
  have hf : HasFiniteDomain (emptyPartition V) := by simp [HasFiniteDomain, emptyPartition]
  exact wins_from_unfriendly_partition G p hp α (emptyPartition V) hf
    (fun _ b h => False.elim (Option.some_ne_none b h.symm))

end TenChallenges.Continuation

end

-- Source: Continuation/UnfriendlyTriangleFreeSix.lean
section

/-!
# Finite replies and degree capacity

The last round depends on the number of assigned same-colour neighbours
and the full size of the queried vertex's neighbourhood.
-/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.TriangleFreeSix

open Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The assigned same-colour neighbours of each vertex use at most half its degree. -/
def LastRoundCapacity (f : V → Option Bool) : Prop :=
  ∀ x b, f x = some b →
    #(NeighColored G f x (some b)) + #(NeighColored G f x (some b)) ≤ #(G.neighborSet x)

/-- The last-round capacity test gives the exact winning positions with finite domain. -/
theorem wins_one_iff_capacity (f : V → Option Bool) (hf : HasFiniteDomain f) :
    PartitionerWins G f (1 : Ordinal.{v}) ↔ LastRoundCapacity G f := by
  classical
  rw [PartitionerWins]
  constructor
  · intro hw x b hb
    obtain ⟨g, hg, _⟩ := hw x 0 zero_lt_one
    obtain ⟨d, hd, hcard⟩ := hg.2.2
    have hdb : d = b := Option.some.inj (hd.symm.trans (hg.1 x b hb))
    subst d
    let S : Set V := G.neighborSet x ∩ f ⁻¹' {some b}
    let T : Set V := G.neighborSet x \ S
    have hs : S ⊆ G.neighborSet x ∩ g ⁻¹' {some b} :=
      fun y hy => ⟨hy.1, hg.1 y b hy.2⟩
    have ht : G.neighborSet x ∩ g ⁻¹' {some (!b)} ⊆ T := by
      intro y hy
      refine ⟨hy.1, ?_⟩
      intro hyS
      exact (Bool.not_eq_self b).mp (Option.some.inj (hy.2.symm.trans (hg.1 y b hyS.2)))
    have h : #S ≤ #T :=
      (Cardinal.mk_le_mk_of_subset hs).trans (hcard.trans (Cardinal.mk_le_mk_of_subset ht))
    change #S + #S ≤ #(G.neighborSet x)
    calc
      #S + #S ≤ #T + #S := by gcongr
      _ = #(G.neighborSet x) :=
        Cardinal.mk_sdiff_add_mk (show S ⊆ G.neighborSet x from Set.inter_subset_left)
  · intro hcap x β hβ
    obtain rfl := Order.lt_one_iff.mp hβ
    by_cases hx : f x = none
    · obtain ⟨b, hb⟩ := minority_update G f x
      exact ⟨Function.update f x (some b),
        ⟨update_extends hx b, finite_update hf x b, hb⟩, wins_zero G _⟩
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
      let S : Set V := G.neighborSet x ∩ f ⁻¹' {some b}
      let T : Set V := G.neighborSet x \ S
      have hS : S.Finite := hf.subset
        (fun y hy hn => Option.some_ne_none b (hy.2.symm.trans hn))
      have hcard : #S ≤ #T := by
        have h := hcap x b hb
        change #S + #S ≤ #(G.neighborSet x) at h
        rw [← Cardinal.mk_sdiff_add_mk (show S ⊆ G.neighborSet x from Set.inter_subset_left)] at h
        change #S + #S ≤ #T + #S at h
        by_cases hT : T.Finite
        · rw [← Set.cast_ncard hS, ← Set.cast_ncard hT] at h ⊢
          exact_mod_cast (show S.ncard ≤ T.ncard by
            exact Nat.le_of_add_le_add_right (by exact_mod_cast h))
        · exact ((Cardinal.mk_lt_aleph0_iff.mpr hS.to_subtype).trans_le
            (Cardinal.aleph0_le_mk_iff.mpr (Set.infinite_coe_iff.mpr hT))).le
      let p : V → Option Bool := fun y => if f y = some b then some b else some (!b)
      have hfp : Extends f p := by
        intro y d hd
        cases b <;> cases d <;> simp [p, hd]
      have hneq : some (!b) ≠ some b := by cases b <;> decide
      have hpSame : (G.neighborSet x ∩ p ⁻¹' {some b}) = S := by
        ext y
        by_cases h : f y = some b <;> simp [p, S, h, hneq]
      have hpOpp : (G.neighborSet x ∩ p ⁻¹' {some (!b)}) = T := by
        ext y
        by_cases h : f y = some b <;> simp [p, T, S, h, Ne.symm hneq]
      have hpuf : UnfriendlyAt G p x := by
        refine ⟨b, by simp [p, hb], ?_⟩
        unfold NeighColored
        rw [hpSame, hpOpp]
        exact hcard
      obtain ⟨g, hg, _⟩ := finite_response_of_unfriendly_partition G p f hf hfp x hpuf
      exact ⟨g, hg, wins_zero G _⟩

/-! ## Finite query patterns

Index zero denotes the most recently added vertex.  A new row records all
edges from a fresh query to the indexed support. -/

private structure Pattern (n : ℕ) where
  adj : Fin n → Fin n → Bool
  color : Fin n → Bool

private def Pattern.add {n : ℕ} (p : Pattern n) (r : Fin n → Bool) (b : Bool) :
    Pattern (n + 1) where
  adj := Fin.cases (Fin.cases false r) (fun i => Fin.cases (r i) (p.adj i))
  color := Fin.cases b p.color

private def countColor {n : ℕ} (p : Pattern n) (i : Fin n) (b : Bool) : ℕ :=
  (Finset.univ.filter fun j => p.adj i j && (p.color j == b)).card

private def balanced {n : ℕ} (p : Pattern n) (i : Fin n) : Bool :=
  countColor p i (p.color i) ≤ countColor p i (!(p.color i))

private def allRows : (n : ℕ) → ((Fin n → Bool) → Bool) → Bool
  | 0, k => k Fin.elim0
  | n + 1, k => allRows n fun r => k (Fin.cases false r) && k (Fin.cases true r)

private def triangleAt {n : ℕ} (p : Pattern n) (i : Fin n) : Bool :=
  (List.finRange n).any fun j => (List.finRange n).any fun l =>
    p.adj i j && p.adj i l && p.adj j l

private def leaf {n : ℕ} (p : Pattern n) (i : Fin n) : Bool :=
  let s := countColor p i (p.color i)
  let o := countColor p i (!(p.color i))
  balanced p i || ((s ≤ 1) || ((s ≤ 2) && (3 ≤ s + o) && triangleAt p i))

private def tree : (k : ℕ) → {n : ℕ} → Pattern n → Bool
  | 0, n, p => (List.finRange n).all (leaf p)
  | k + 1, n, p =>
    tree k p && ((List.finRange n).all (balanced p) && allRows n fun r =>
      [false, true].any fun b => balanced (p.add r b) 0 && tree k (p.add r b))

private structure Realization {n : ℕ} (p : Pattern n) (f : V → Option Bool) where
  vertex : Fin n ↪ V
  edge : ∀ i j, p.adj i j = true ↔ G.Adj (vertex i) (vertex j)
  assigned : ∀ i, f (vertex i) = some (p.color i)
  covers : ∀ x, f x ≠ none → ∃ i, vertex i = x

private theorem allRows_sound {n : ℕ} {k : (Fin n → Bool) → Bool}
    (h : allRows n k = true) (r : Fin n → Bool) : k r = true := by
  induction n with
  | zero => exact (congrArg k (Subsingleton.elim Fin.elim0 r)).symm ▸ h
  | succ n ih =>
    have hboth := Bool.and_eq_true_iff.mp (ih h (Fin.tail r))
    exact (Fin.cons_self_tail r) ▸ (Bool.eq_false_or_eq_true (r 0)).elim
      (fun e => e.symm ▸ hboth.2) (fun e => e.symm ▸ hboth.1)


private theorem Realization.count_eq {n : ℕ} {p : Pattern n} {f : V → Option Bool}
    (h : Realization G p f) (i : Fin n) (b : Bool) :
    #(NeighColored G f (h.vertex i) (some b)) = (countColor p i b : Cardinal) := by
  classical
  let s := Finset.univ.filter fun j => p.adj i j && (p.color j == b)
  have hset : G.neighborSet (h.vertex i) ∩ f ⁻¹' {some b} = (s.map h.vertex : Finset V) := by
    ext y
    simp only [s, Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq, h.edge]
    exact ⟨fun ⟨ha, hy⟩ => let ⟨j, e⟩ := h.covers y (hy ▸ Option.some_ne_none b)
      ⟨j, ⟨e ▸ ha, Option.some.inj ((h.assigned j).symm.trans (e ▸ hy))⟩, e⟩,
      fun ⟨j, ⟨ha, hc⟩, e⟩ => e ▸ ⟨ha, hc ▸ h.assigned j⟩⟩
  simp [NeighColored, hset, Cardinal.mk_fintype, s, countColor,
    Finset.card_image_of_injective _ h.vertex.injective]

private theorem Realization.unfriendly {n : ℕ} {p : Pattern n} {f : V → Option Bool}
    (h : Realization G p f) (i : Fin n) (hb : balanced p i = true) :
    UnfriendlyAt G f (h.vertex i) := by
  exact ⟨p.color i, h.assigned i, by simpa only [h.count_eq, Nat.cast_le] using
    (show countColor p i (p.color i) ≤ countColor p i (!(p.color i)) from of_decide_eq_true hb)⟩

private theorem assigned_le_degree (f : V → Option Bool) (x : V) (d : Bool) :
    #(NeighColored G f x (some d)) + #(NeighColored G f x (some (!d))) ≤ #(G.neighborSet x) := by
  let s := G.neighborSet x ∩ f ⁻¹' {some d}
  let t := G.neighborSet x ∩ f ⁻¹' {some (!d)}
  have hdis : Disjoint s t := Set.disjoint_left.mpr fun y hy ht =>
    Bool.not_ne_self d (Option.some.inj (ht.2.symm.trans hy.2))
  exact (Cardinal.mk_union_of_disjoint hdis) ▸
    Cardinal.mk_le_mk_of_subset (show s ∪ t ⊆ G.neighborSet x from
      Set.union_subset Set.inter_subset_left Set.inter_subset_left)

private theorem capacity_at_of_unfriendly {f : V → Option Bool} {x : V} {b : Bool}
    (hx : f x = some b) (hu : UnfriendlyAt G f x) :
    #(NeighColored G f x (some b)) + #(NeighColored G f x (some b)) ≤ #(G.neighborSet x) := by
  obtain ⟨d, hd, hcard⟩ := hu
  obtain rfl := Option.some.inj (hd.symm.trans hx)
  exact (add_le_add_right hcard _).trans (assigned_le_degree G f x d)

private def Realization.row {n : ℕ} {p : Pattern n} {f : V → Option Bool}
    (h : Realization G p f) [DecidableRel G.Adj] (x : V) (i : Fin n) : Bool :=
  decide (G.Adj x (h.vertex i))

private def Realization.add {n : ℕ} {p : Pattern n} {f : V → Option Bool}
    (h : Realization G p f) [DecidableRel G.Adj] [DecidableEq V] {x : V} (hx : f x = none)
    (b : Bool) : Realization G (p.add (h.row G x) b) (Function.update f x (some b)) := by
  have fresh : x ∉ Set.range h.vertex := fun ⟨i, e⟩ =>
    Option.some_ne_none (p.color i) ((h.assigned i).symm.trans (e ▸ hx))
  refine ⟨⟨Fin.cons x h.vertex, Fin.cons_injective_iff.mpr ⟨fresh, h.vertex.injective⟩⟩,
    ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Pattern.add, row, h.edge, G.adj_comm]
  · exact Fin.cases (Function.update_self ..)
      (fun i => (Function.update_of_ne (fun e => fresh ⟨i, e⟩) ..).trans (h.assigned i))
  · exact fun y hy => (eq_or_ne y x).elim (fun e => ⟨0, e.symm⟩) fun e =>
      let ⟨i, hi⟩ := h.covers y (by simpa only [Function.update_of_ne e] using hy)
      ⟨i.succ, hi⟩

private theorem Realization.triangle {n : ℕ} {p : Pattern n} {f : V → Option Bool}
    (h : Realization G p f) {i : Fin n} (ht : triangleAt p i = true) :
    ∃ y z, G.Adj (h.vertex i) y ∧ G.Adj (h.vertex i) z ∧ G.Adj y z := by
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp ht
  obtain ⟨l, _, hl⟩ := List.any_eq_true.mp hj
  obtain ⟨hij, hjl⟩ := Bool.and_eq_true_iff.mp hl
  exact ⟨h.vertex j, h.vertex l, (h.edge i j).mp (Bool.and_eq_true_iff.mp hij).1,
    (h.edge i l).mp (Bool.and_eq_true_iff.mp hij).2, (h.edge j l).mp hjl⟩

private theorem tree_sound
    (ht : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      3 ≤ #(G.neighborSet x) → 4 ≤ #(G.neighborSet x))
    (hdeg : ∀ x, 2 ≤ #(G.neighborSet x)) (k : ℕ) {n : ℕ} {p : Pattern n}
    {f : V → Option Bool} (h : Realization G p f) (hf : HasFiniteDomain f)
    (hc : tree k p = true) : PartitionerWins G f ((k + 1 : ℕ) : Ordinal.{v}) := by
  classical
  induction k generalizing n f with
  | zero =>
    rw [Nat.zero_add, Nat.cast_one, wins_one_iff_capacity G f hf]
    intro x b hx
    obtain ⟨i, rfl⟩ := h.covers x (hx ▸ Option.some_ne_none b)
    obtain rfl := Option.some.inj ((h.assigned i).symm.trans hx)
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hc i (List.mem_finRange i)) with hb | hs
    · exact capacity_at_of_unfriendly G hx (h.unfriendly G i hb)
    · rcases Bool.or_eq_true_iff.mp hs with hs1 | hs2
      · refine le_trans ?_ (hdeg (h.vertex i))
        simp only [h.count_eq, ← Nat.cast_add]
        exact_mod_cast (show countColor p i (p.color i) + countColor p i (p.color i) ≤ 2 by
          have := of_decide_eq_true hs1
          omega)
      · obtain ⟨hn, htri⟩ := Bool.and_eq_true_iff.mp hs2
        obtain ⟨y, z, hxy, hxz, hyz⟩ := h.triangle G htri
        have hd := assigned_le_degree G f (h.vertex i) (p.color i)
        simp only [h.count_eq, ← Nat.cast_add] at hd
        have h3 : (3 : Cardinal) ≤ #(G.neighborSet (h.vertex i)) := le_trans
          (by exact_mod_cast of_decide_eq_true (Bool.and_eq_true_iff.mp hn).2) hd
        refine le_trans ?_ (ht _ y z hxy hxz hyz h3)
        simp only [h.count_eq, ← Nat.cast_add]
        exact_mod_cast (show countColor p i (p.color i) + countColor p i (p.color i) ≤ 4 by
          have := of_decide_eq_true (Bool.and_eq_true_iff.mp hn).1
          omega)
  | succ k ih =>
    obtain ⟨hold, hstep⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hbal, hrow⟩ := Bool.and_eq_true_iff.mp hstep
    rw [PartitionerWins]
    intro x β hβ
    have hle : β ≤ ((k + 1 : ℕ) : Ordinal) :=
      Order.lt_add_one_iff.mp ((Nat.cast_add_one (R := Ordinal) (k + 1)) ▸ hβ)
    by_cases hx : f x = none
    · have hchoice := allRows_sound hrow (h.row G x)
      obtain ⟨b, _, hb⟩ := List.any_eq_true.mp hchoice
      obtain ⟨hnew, hnext⟩ := Bool.and_eq_true_iff.mp hb
      let h' := h.add G hx b
      exact ⟨_, ⟨update_extends hx b, finite_update hf x b, h'.unfriendly G 0 hnew⟩,
        wins_mono G hle (ih h' (finite_update hf x b) hnext)⟩
    · obtain ⟨i, rfl⟩ := h.covers x hx
      exact ⟨f, ⟨fun _ _ e => e, hf, h.unfriendly G i (List.all_eq_true.mp hbal i
        (List.mem_finRange i))⟩, wins_mono G hle (ih h hf hold)⟩

private def stableTree : (k : ℕ) → {n : ℕ} → Pattern n → Bool
  | 0, n, p => (List.finRange n).all (balanced p)
  | k + 1, n, p =>
    stableTree k p && allRows n fun r =>
      [false, true].any fun b => stableTree k (p.add r b)

private theorem stableTree.balanced {k n : ℕ} {p : Pattern n}
    (h : stableTree k p = true) (i : Fin n) : balanced p i = true := by
  induction k with
  | zero => exact List.all_eq_true.mp h i (List.mem_finRange i)
  | succ k ih => exact ih (Bool.and_eq_true_iff.mp h).1

private theorem stableTree.sound (k : ℕ) {n : ℕ} {p : Pattern n}
    {f : V → Option Bool} (h : Realization G p f) (hf : HasFiniteDomain f)
    (hc : stableTree k p = true) : PartitionerWins G f ((k + 1 : ℕ) : Ordinal.{v}) := by
  classical
  induction k generalizing n f with
  | zero =>
    rw [Nat.zero_add, Nat.cast_one]
    exact stable_wins_one G hf fun x b hx =>
      let ⟨i, e⟩ := h.covers x (hx ▸ Option.some_ne_none b)
      e ▸ h.unfriendly G i (stableTree.balanced hc i)
  | succ k ih =>
    obtain ⟨hold, hrow⟩ := Bool.and_eq_true_iff.mp hc
    rw [PartitionerWins]
    intro x β hβ
    have hle : β ≤ ((k + 1 : ℕ) : Ordinal) :=
      Order.lt_add_one_iff.mp ((Nat.cast_add_one (R := Ordinal) (k + 1)) ▸ hβ)
    by_cases hx : f x = none
    · obtain ⟨b, _, hnext⟩ := List.any_eq_true.mp (allRows_sound hrow (h.row G x))
      let h' := h.add G hx b
      exact ⟨_, ⟨update_extends hx b, finite_update hf x b,
        h'.unfriendly G 0 (stableTree.balanced hnext 0)⟩,
        wins_mono G hle (ih h' (finite_update hf x b) hnext)⟩
    · obtain ⟨i, rfl⟩ := h.covers x hx
      exact ⟨f, ⟨fun _ _ e => e, hf, h.unfriendly G i (stableTree.balanced hold i)⟩,
        wins_mono G hle (ih h hf hold)⟩

private def starPattern (b : Bool) : Pattern 3 where
  adj i j := (i == 0) != (j == 0)
  color i := if i = 0 then b else !b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_star (b : Bool) : stableTree 2 (starPattern b) = true := by
  cases b <;> decide

/-- A properly coloured two-leaf star with no other assigned vertices wins three rounds. -/
theorem win_three_of_colored_star {f : V → Option Bool} (v : Fin 3 ↪ V) (b : Bool)
    (h01 : G.Adj (v 0) (v 1)) (h02 : G.Adj (v 0) (v 2))
    (h12 : ¬ G.Adj (v 1) (v 2))
    (h0 : f (v 0) = some b) (h1 : f (v 1) = some (!b)) (h2 : f (v 2) = some (!b))
    (hcover : ∀ x, f x ≠ none → ∃ i, v i = x) :
    PartitionerWins G f (3 : Ordinal.{v}) := by
  let h : Realization G (starPattern b) f :=
    ⟨v, by
      simp [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        starPattern, h01, h02, h12, h01.symm, h02.symm,
        show ¬ G.Adj (v 2) (v 1) from fun ha => h12 ha.symm],
      by
        simp [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          starPattern, h0, h1, h2],
      hcover⟩
  exact_mod_cast stableTree.sound G 2 h ((Set.finite_range v).subset hcover) (checked_star b)

end TenChallenges.Continuation.TriangleFreeSix

end

-- Source: Continuation/UnfriendlyNamedPositions.lean
section

/-! # Finite diagrams for checking replies with auxiliary vertices

A diagram names finitely many vertices. It may name a potential witness before
assigning it a colour. The degree lower bounds include neighbours outside the diagram.
-/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.NamedPositions

open scoped Cardinal
open _root_.Continuation.TC10

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

abbrev Edges (n : ℕ) := Fin n → Fin n → Bool
abbrev Colours (n : ℕ) := Fin n → Option Bool

noncomputable def position (e : Fin n ↪ V) (p : Colours n) : V → Option Bool :=
  Function.extend e p (fun _ => none)

@[simp] theorem position_name (e : Fin n ↪ V) (p : Colours n) (i : Fin n) :
    position e p (e i) = p i := e.injective.extend_apply _ _ _

theorem position_outside {e : Fin n ↪ V} (p : Colours n) {x : V} (hx : x ∉ Set.range e) :
    position e p x = none := Function.extend_apply' _ _ _ hx

theorem position_finite (e : Fin n ↪ V) (p : Colours n) : HasFiniteDomain (position e p) :=
  (Set.finite_range e).subset fun _ hx => Classical.byContradiction fun hn =>
    hx (position_outside p hn)

/-- The adjacency matrix on the named vertices is exact. -/
def Realizes (e : Fin n ↪ V) (A : Edges n) : Prop :=
  ∀ i j, A i j = true ↔ G.Adj (e i) (e j)

def count (A : Edges n) (p : Colours n) (i : Fin n) (b : Bool) : ℕ :=
  (Finset.univ.filter fun j => A i j && (p j == some b)).card

def namedDegree (A : Edges n) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => A i j).card

def Balanced (A : Edges n) (p : Colours n) (i : Fin n) : Prop :=
  ∃ b, p i = some b ∧ count A p i b ≤ count A p i (!b)

def Capacity (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) : Prop :=
  ∀ i b, p i = some b → 2 * count A p i b ≤ max (namedDegree A i) (lo i)

def CanReply (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) (i : Fin n) : Prop :=
  ∃ q : Colours n, Extends p q ∧ Balanced A q i ∧ Capacity A lo q

theorem count_eq {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A) (p : Colours n)
    (i : Fin n) (b : Bool) :
    #(NeighColored G (position e p) (e i) (some b)) = (count A p i b : Cardinal) := by
  classical
  let s := Finset.univ.filter fun j => A i j && (p j == some b)
  have hset : G.neighborSet (e i) ∩ position e p ⁻¹' {some b} = (s.map e : Finset V) := by
    ext y
    simp only [s, Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨ha, hy⟩
      have hmem : y ∈ Set.range e := Classical.byContradiction fun hn =>
        Option.some_ne_none b (hy.symm.trans (position_outside p hn))
      obtain ⟨j, rfl⟩ := hmem
      exact ⟨j, ⟨(he i j).mpr ha, (position_name e p j).symm.trans hy⟩, rfl⟩
    · rintro ⟨j, ⟨ha, hc⟩, rfl⟩
      exact ⟨(he i j).mp ha, (position_name e p j).trans hc⟩
  simp [NeighColored, hset, Cardinal.mk_fintype, s, count,
    Finset.card_image_of_injective _ e.injective]

theorem namedDegree_le {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A) (i : Fin n) :
    (namedDegree A i : Cardinal) ≤ #(G.neighborSet (e i)) := by
  have hcount := count_eq G he (fun _ => some true) i true
  simp only [count, beq_self_eq_true, Bool.and_true] at hcount
  rw [namedDegree, ← hcount]
  exact Cardinal.mk_le_mk_of_subset Set.inter_subset_left

theorem capacity_sound {e : Fin n ↪ V} {A : Edges n} {p : Colours n} {lo : Fin n → ℕ}
    (he : Realizes G e A) (hl : ∀ i, (lo i : Cardinal) ≤ #(G.neighborSet (e i)))
    (hc : Capacity A lo p) :
    PartitionerWins G (position e p) (1 : Ordinal.{v}) := by
  apply (TriangleFreeSix.wins_one_iff_capacity G _ (position_finite e p)).2
  intro x b hx
  have hxmem : x ∈ Set.range e := Classical.byContradiction fun hn =>
    Option.some_ne_none b (hx.symm.trans (position_outside p hn))
  obtain ⟨i, rfl⟩ := hxmem
  rw [count_eq G he]
  rcases le_max_iff.mp (hc i b ((position_name e p i).symm.trans hx)) with h | h
  · exact le_trans (by exact_mod_cast (by simpa only [two_mul] using h :
      count A p i b + count A p i b ≤ namedDegree A i)) (namedDegree_le G he i)
  · exact le_trans (by exact_mod_cast (by simpa only [two_mul] using h :
      count A p i b + count A p i b ≤ lo i)) (hl i)

theorem response_sound {e : Fin n ↪ V} {A : Edges n} {p : Colours n} {lo : Fin n → ℕ}
    (he : Realizes G e A) (hl : ∀ i, (lo i : Cardinal) ≤ #(G.neighborSet (e i)))
    (i : Fin n) (hr : CanReply A lo p i) :
    ∃ g, IsLegalResponse G (position e p) g (e i) ∧ PartitionerWins G g (1 : Ordinal.{v}) := by
  obtain ⟨q, hpq, ⟨b, hbi, hbal⟩, hcap⟩ := hr
  refine ⟨position e q, ⟨?_, position_finite e q, b, (position_name e q i).trans hbi, ?_⟩,
    capacity_sound G he hl hcap⟩
  · intro x d hx
    by_cases hm : x ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hm
      simpa only [position_name] using hpq j d ((position_name e p j).symm.trans hx)
    · simp [position_outside p hm] at hx
  · simpa only [count_eq G he, Nat.cast_le] using hbal

/-- Extend a diagram by a vertex whose adjacencies to the old names form the given row. -/
def addRow (A : Edges n) (r : Fin n → Bool) : Edges (n + 1) :=
  Fin.cases (Fin.cons false r) (fun i => Fin.cons (r i) (A i))

private def addName (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) : Fin (n + 1) ↪ V :=
  ⟨Fin.cons x e, Fin.cons_injective_iff.mpr ⟨hx, e.injective⟩⟩

private lemma addName_none (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) (p : Colours n) :
    position (addName e x hx) (Fin.cons none p) = position e p := by
  funext y
  by_cases hm : y ∈ Set.range (addName e x hx)
  · obtain ⟨j, rfl⟩ := hm
    rw [position_name]
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (position_outside p hx).symm
    · exact (position_name e p k).symm
  · have hout : y ∉ Set.range e := fun ⟨k, hk⟩ => hm ⟨k.succ, hk⟩
    rw [position_outside _ hm, position_outside _ hout]

private lemma realizes_add {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A)
    (x : V) (hx : x ∉ Set.range e) (r : Fin n → Bool)
    (hr : ∀ i, r i = true ↔ G.Adj x (e i)) :
    Realizes G (addName e x hx) (addRow A r) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    first | exact he _ _ | simp [addRow, addName, hr, G.adj_comm]

/-- Every named query has a reply, as does every possible new adjacency row. -/
def TwoRounds (A : Edges n) (lo : Fin n → ℕ) (sealed : Fin n → Bool)
    (d : ℕ) (p : Colours n) : Prop :=
  (∀ i, CanReply A lo p i) ∧
  ∀ r : Fin n → Bool, (∀ i, sealed i = true → r i = false) →
    CanReply (addRow A r) (Fin.cons d lo) (Fin.cons none p) 0

theorem twoRounds_sound {e : Fin n ↪ V} {A : Edges n} {lo : Fin n → ℕ}
    {sealed : Fin n → Bool} {d : ℕ} {p : Colours n}
    (he : Realizes G e A) (hl : ∀ i, (lo i : Cardinal) ≤ #(G.neighborSet (e i)))
    (hs : ∀ i, sealed i = true → G.neighborSet (e i) ⊆ Set.range e)
    (hd : ∀ x ∉ Set.range e, (d : Cardinal) ≤ #(G.neighborSet x))
    (ht : TwoRounds A lo sealed d p) :
    PartitionerWins G (position e p) (2 : Ordinal.{v}) := by
  classical
  rw [PartitionerWins]
  intro x β hβ
  suffices h : ∃ g, IsLegalResponse G (position e p) g x ∧
      PartitionerWins G g (1 : Ordinal.{v}) by
    obtain ⟨g, hg, hw⟩ := h
    have hle : β ≤ 1 := Order.lt_add_one_iff.mp (by simpa only [one_add_one_eq_two] using hβ)
    exact ⟨g, hg, wins_mono G hle hw⟩
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    exact response_sound G he hl i (ht.1 i)
  · let r (i : Fin n) := decide (G.Adj x (e i))
    have hr : ∀ i, r i = true ↔ G.Adj x (e i) := fun _ => decide_eq_true_iff
    have hsealed (i : Fin n) (hi : sealed i = true) : r i = false :=
      decide_eq_false (fun ha : G.Adj x (e i) => hx (hs i hi ha.symm))
    let newBounds : Fin (n + 1) → ℕ := Fin.cons d lo
    have hlo (j : Fin (n + 1)) :
        (newBounds j : Cardinal) ≤ #(G.neighborSet (addName e x hx j)) :=
      Fin.cases (motive := fun j => (newBounds j : Cardinal) ≤
        #(G.neighborSet (addName e x hx j))) (hd x hx) (fun i => hl i) j
    have hresp := response_sound G (realizes_add G he x hx r hr) hlo 0 (ht.2 r hsealed)
    rw [addName_none] at hresp
    exact hresp

end TenChallenges.Continuation.NamedPositions

end

-- Source: Continuation/UnfriendlyEdgeIsolate.lean
section

/-! # Three remaining rounds at an edge and an isolated coloured vertex -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.NamedPositions

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

/-- The neighbours of a named vertex that are also named in the diagram. -/
def namedNeighbors (e : Fin n ↪ V) (A : Edges n) (i : Fin n) : Finset V :=
  (Finset.univ.filter fun j => A i j).map e

theorem mem_namedNeighbors {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A)
    (i : Fin n) (x : V) :
    x ∈ namedNeighbors e A i ↔ G.Adj (e i) x ∧ x ∈ Set.range e := by
  simp only [namedNeighbors, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hij, rfl⟩
    exact ⟨(he i j).mp hij, ⟨j, rfl⟩⟩
  · rintro ⟨hx, j, rfl⟩
    exact ⟨j, (he i j).mpr hx, rfl⟩

@[simp] theorem card_namedNeighbors (e : Fin n ↪ V) (A : Edges n) (i : Fin n) :
    (namedNeighbors e A i).card = namedDegree A i := by
  simp [namedNeighbors, namedDegree]

theorem neighborSet_eq_namedNeighbors {e : Fin n ↪ V} {A : Edges n}
    (he : Realizes G e A) (i : Fin n) (hseal : G.neighborSet (e i) ⊆ Set.range e) :
    G.neighborSet (e i) = (↑(namedNeighbors e A i) : Set V) := by
  ext x
  exact (mem_namedNeighbors G he i x).trans (and_iff_left_of_imp fun hx => hseal hx) |>.symm

theorem degree_eq_namedDegree {e : Fin n ↪ V} {A : Edges n}
    (he : Realizes G e A) (i : Fin n) (hseal : G.neighborSet (e i) ⊆ Set.range e) :
    #(G.neighborSet (e i)) = (namedDegree A i : Cardinal) := by
  simp [neighborSet_eq_namedNeighbors G he i hseal, Cardinal.mk_fintype]

theorem add_one_le_degree_of_freshNeighbor {e : Fin n ↪ V} {A : Edges n} {x : V}
    (he : Realizes G e A) (i : Fin n) (hax : G.Adj (e i) x) (hx : x ∉ Set.range e) :
    (namedDegree A i : Cardinal) + 1 ≤ #(G.neighborSet (e i)) := by
  classical
  have hmem : x ∉ namedNeighbors e A i := fun h => hx ((mem_namedNeighbors G he i x).mp h).2
  have hsub : (↑(insert x (namedNeighbors e A i)) : Set V) ⊆ G.neighborSet (e i) := by
    intro y hy
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy'
    · exact hax
    · exact (mem_namedNeighbors G he i y).mp hy' |>.1
  calc
    (namedDegree A i : Cardinal) + 1 = #(↑(insert x (namedNeighbors e A i)) : Set V) := by
      simp [Cardinal.mk_fintype, Finset.card_insert_of_notMem hmem]
    _ ≤ _ := Cardinal.mk_le_mk_of_subset hsub

theorem exists_freshNeighbor_iff {e : Fin n ↪ V} {A : Edges n}
    (he : Realizes G e A) (i : Fin n) :
    (∃ x, G.Adj (e i) x ∧ x ∉ Set.range e) ↔
      (namedDegree A i : Cardinal) + 1 ≤ #(G.neighborSet (e i)) := by
  refine ⟨fun ⟨x, hax, hx⟩ => add_one_le_degree_of_freshNeighbor G he i hax hx, ?_⟩
  intro hdeg
  by_contra hfresh
  have hseal : G.neighborSet (e i) ⊆ Set.range e := fun x hx =>
    Classical.byContradiction fun hout => hfresh ⟨x, hx, hout⟩
  rw [degree_eq_namedDegree G he i hseal] at hdeg
  exact (not_lt_of_ge hdeg) (by exact_mod_cast Nat.lt_succ_self (namedDegree A i))

theorem exists_freshNeighbor_of_degree_four {e : Fin n ↪ V} {A : Edges n}
    (he : Realizes G e A) (i : Fin n) (hthree : namedDegree A i = 3)
    (hdeg : 4 ≤ #(G.neighborSet (e i))) :
    ∃ x, G.Adj (e i) x ∧ x ∉ Set.range e := by
  apply (exists_freshNeighbor_iff G he i).mpr
  simpa only [hthree, Nat.cast_ofNat, three_add_one_eq_four] using hdeg

end TenChallenges.Continuation.NamedPositions

namespace TenChallenges.Continuation.NamedPositions

variable {n : ℕ}

def ReplyWith (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) (i : Fin n)
    (q : Colours n) : Prop :=
  Extends p q ∧ Balanced A q i ∧ Capacity A lo q

instance (A : Edges n) (p : Colours n) (i : Fin n) : Decidable (Balanced A p i) := by
  unfold Balanced
  infer_instance

instance (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) : Decidable (Capacity A lo p) := by
  unfold Capacity
  infer_instance

instance (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) (i : Fin n)
    (q : Colours n) : Decidable (ReplyWith A lo p i q) := by
  unfold ReplyWith Extends
  infer_instance

def bcWitness (za zb zx : Bool) : Edges 5 :=
  ![![false, true, false, false, za],
    ![true, false, false, true, zb],
    ![false, false, false, true, true],
    ![false, true, true, false, zx],
    ![za, zb, true, zx, false]]

def bcColours : Colours 5 := ![some false, some true, some false, some false, none]

def bcNamedReply (i : Fin 5) : Colours 5 :=
  ![some false, some true, some false, some false, if i == 2 || i == 4 then some true else none]

def bcFreshReply (r : Fin 5 → Bool) : Colours 6 :=
  Fin.cons (some (r 2 || r 3 || (r 0 && !r 1))) bcColours

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_bc_named : ∀ za zb zx : Bool, ∀ i : Fin 5,
    ReplyWith (bcWitness za zb zx) (fun _ => 2) bcColours i (bcNamedReply i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_bc_fresh : ∀ za zb zx : Bool, ∀ r : Fin 5 → Bool,
    ReplyWith (addRow (bcWitness za zb zx) r) (Fin.cons 2 (fun _ => 2)) (Fin.cons none bcColours) 0
      (bcFreshReply r) := by
  decide +kernel

theorem checked_bc (za zb zx : Bool) :
    Balanced (bcWitness za zb zx) bcColours 3 ∧
    TwoRounds (bcWitness za zb zx) (fun _ => 2) (fun _ => false) 2 bcColours := by
  exact ⟨(checked_bc_named za zb zx 3).2.1,
    fun i => ⟨bcNamedReply i, checked_bc_named za zb zx i⟩,
    fun r _ => ⟨bcFreshReply r, checked_bc_fresh za zb zx r⟩⟩


structure ReplyPlan (n : ℕ) where
  named : Fin n → Colours n
  fresh : (Fin n → Bool) → Colours (n + 1)

def CheckedPlan (A : Edges n) (lo : Fin n → ℕ) (sealed : Fin n → Bool)
    (d : ℕ) (p : Colours n) (x : Fin n) (plan : ReplyPlan n) : Prop :=
  Balanced A p x ∧ (∀ i, ReplyWith A lo p i (plan.named i)) ∧
    ∀ r : Fin n → Bool, (∀ i, sealed i = true → r i = false) →
      ReplyWith (addRow A r) (Fin.cons d lo) (Fin.cons none p) 0 (plan.fresh r)

instance (A : Edges n) (lo : Fin n → ℕ) (sealed : Fin n → Bool)
    (d : ℕ) (p : Colours n) (x : Fin n) (plan : ReplyPlan n) :
    Decidable (CheckedPlan A lo sealed d p x plan) := by
  unfold CheckedPlan
  infer_instance

theorem checkedPlan_sound {A : Edges n} {lo : Fin n → ℕ} {sealed : Fin n → Bool}
    {d : ℕ} {p : Colours n} {x : Fin n} {plan : ReplyPlan n}
    (h : CheckedPlan A lo sealed d p x plan) : Balanced A p x ∧ TwoRounds A lo sealed d p :=
  ⟨h.1, fun i => ⟨plan.named i, h.2.1 i⟩, fun r hr => ⟨plan.fresh r, h.2.2 r hr⟩⟩

def singletonReply (A : Edges n) (lo : Fin n → ℕ) (p : Colours n) (i : Fin n) :
    Colours n :=
  let q := Function.update p i (some false)
  if ReplyWith A lo p i q then q else Function.update p i (some true)

def singletonPlan (A : Edges n) (lo : Fin n → ℕ) (d : ℕ) (p : Colours n)
    (extra : Fin n → Option (Colours n) := fun _ => none) : ReplyPlan n where
  named i := (extra i).getD (singletonReply A lo p i)
  fresh r := singletonReply (addRow A r) (Fin.cons d lo) (Fin.cons none p) 0

def appendRow (A : Edges n) (r : Fin n → Bool) : Edges (n + 1) :=
  Fin.snoc (fun i => Fin.snoc (A i) (r i)) (Fin.snoc r false)

def edge4 (xa xb xc : Bool) : Edges 4 :=
  ![![false, true, false, xa], ![true, false, false, xb],
    ![false, false, false, xc], ![xa, xb, xc, false]]

def initial4 (b : Bool) : Colours 4 := ![some false, some true, some false, some b]

def bSealed4 : Fin 4 → Bool := ![false, true, false, false]
def bSealed5 : Fin 5 → Bool := Fin.snoc bSealed4 false
def bSealed6 : Fin 6 → Bool := Fin.snoc bSealed5 false
def bySealed6 : Fin 6 → Bool := ![false, true, false, false, true, false]

def xyzInitial (x y z : Option Bool) : Colours 6 := ![some false, some true, some false, x, y, z]
def abc4 : Edges 4 := edge4 true true true
def abc5 (ya yc yx : Bool) : Edges 5 := appendRow abc4 ![ya, true, yc, yx]
def abcTwin5 : Edges 5 := abc5 true true false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_edge4 : ∀ xa xb xc : Bool, !(xb && xc) = true →
    let A := edge4 xa xb xc
    let p := initial4 (!xb && (xa || xc))
    CheckedPlan A (fun _ => 2) (fun _ => false) 2 p 3 (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_abc_b_ge4 :
    let p := initial4 true
    let lo : Fin 4 → ℕ := ![2, 4, 2, 2]
    CheckedPlan abc4 lo (fun _ => false) 2 p 3 (singletonPlan abc4 lo 2 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_abc_b_degree2 :
    let p := initial4 true
    CheckedPlan abc4 (fun _ => 2) bSealed4 2 p 3 (singletonPlan abc4 (fun _ => 2) 2 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_abc_ordinary_y : ∀ ya yc yx : Bool, !(ya && yc && !yx) = true →
    let A := abc5 ya yc yx
    let p := Fin.snoc (initial4 true) none
    CheckedPlan A (fun _ => 2) bSealed5 2 p 3 (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_abc_extra_y_witness : ∀ za zc zx : Bool,
    let A := appendRow abcTwin5 ![za, false, zc, zx, true]
    let p := xyzInitial (some true) none none
    let extra (i : Fin 6) := if i = 4 then some (xyzInitial (some true) (some false) (some true)) else none
    CheckedPlan A (fun _ => 2) bSealed6 2 p 3 (singletonPlan A (fun _ => 2) 2 p extra) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_abc_extra_x_witness : ∀ za zc : Bool,
    let A := appendRow abcTwin5 ![za, false, zc, true, false]
    let p := xyzInitial (some false) (some true) (some true)
    CheckedPlan A (fun _ => 2) bySealed6 2 p 3 (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

end TenChallenges.Continuation.NamedPositions

namespace TenChallenges.Continuation.NamedPositions

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

/-- A first move certified by a checked reply plan leaves two winning rounds. -/
theorem diagram_graph_reply {e : Fin n ↪ V} {A : Edges n} {lo : Fin n → ℕ}
    {sealed : Fin n → Bool} {d : ℕ} {f p : Colours n} {i : Fin n}
    (he : Realizes G e A) (hl : ∀ j, (lo j : Cardinal) ≤ #(G.neighborSet (e j)))
    (hs : ∀ j, sealed j = true → G.neighborSet (e j) ⊆ Set.range e)
    (hd : ∀ x ∉ Set.range e, (d : Cardinal) ≤ #(G.neighborSet x))
    (hExt : Extends f p) (hp : Balanced A p i ∧ TwoRounds A lo sealed d p) :
    ∃ g, IsLegalResponse G (position e f) g (e i) ∧ PartitionerWins G g (2 : Ordinal.{v}) := by
  obtain ⟨⟨b, hb, hbal⟩, hrounds⟩ := hp
  refine ⟨position e p, ⟨?_, position_finite e p, b, (position_name e p i).trans hb, ?_⟩,
    twoRounds_sound G he hl hs hd hrounds⟩
  · intro x c hx
    by_cases hxname : x ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hxname
      simpa only [position_name] using hExt j c ((position_name e f j).symm.trans hx)
    · simp [position_outside f hxname] at hx
  · simpa only [count_eq G he, Nat.cast_le] using hbal

/-- A first move certified by a checked reply plan leaves two winning rounds. -/
theorem checkedPlan_graph_reply {e : Fin n ↪ V} {A : Edges n} {lo : Fin n → ℕ}
    {sealed : Fin n → Bool} {d : ℕ} {f p : Colours n} {i : Fin n} {plan : ReplyPlan n}
    (he : Realizes G e A) (hl : ∀ j, (lo j : Cardinal) ≤ #(G.neighborSet (e j)))
    (hs : ∀ j, sealed j = true → G.neighborSet (e j) ⊆ Set.range e)
    (hd : ∀ x ∉ Set.range e, (d : Cardinal) ≤ #(G.neighborSet x))
    (hExt : Extends f p) (hp : CheckedPlan A lo sealed d p i plan) :
    ∃ g, IsLegalResponse G (position e f) g (e i) ∧ PartitionerWins G g (2 : Ordinal.{v}) :=
  diagram_graph_reply G he hl hs hd hExt (checkedPlan_sound hp)

/-- Append a new named vertex after the existing names. -/
def appendName (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) : Fin (n + 1) ↪ V :=
  ⟨Fin.snoc e x, Fin.snoc_injective_iff.mpr ⟨e.injective, hx⟩⟩

@[simp] theorem appendName_castSucc (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) (i : Fin n) :
    appendName e x hx i.castSucc = e i := by simp [appendName]

@[simp] theorem appendName_last (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) :
    appendName e x hx (Fin.last n) = x := by simp [appendName]

@[simp] theorem range_appendName (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) :
    Set.range (appendName e x hx) = insert x (Set.range e) := Fin.range_snoc _ _

theorem realizes_appendRow {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A)
    (x : V) (hx : x ∉ Set.range e) (r : Fin n → Bool)
    (hr : ∀ i, r i = true ↔ G.Adj x (e i)) :
    Realizes G (appendName e x hx) (appendRow A r) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [appendRow, hr, G.adj_comm]
  exact he _ _

theorem position_append_none (e : Fin n ↪ V) (x : V) (hx : x ∉ Set.range e) (p : Colours n) :
    position (appendName e x hx) (Fin.snoc p none) = position e p := by
  funext y
  by_cases hmem : y ∈ Set.range (appendName e x hx)
  · obtain ⟨j, rfl⟩ := hmem
    rw [position_name]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using (position_outside p hx).symm
    · simp
  · have hy : y ∉ Set.range e := fun ⟨i, hi⟩ =>
      hmem ⟨i.castSucc, by simpa using hi⟩
    rw [position_outside _ hmem, position_outside _ hy]

def edge3 : Edges 3 :=
  ![![false, true, false], ![true, false, false], ![false, false, false]]

def edgeColours3 : Colours 3 := ![some false, some true, some false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_edge3 : ∀ i : Fin 3,
    CheckedPlan edge3 (fun _ => 2) (fun _ => false) 2 edgeColours3 i
      (singletonPlan edge3 (fun _ => 2) 2 edgeColours3) := by
  decide +kernel

theorem edge_isolate_named_reply {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ x, (2 : Cardinal) ≤ #(G.neighborSet x)) (i : Fin 3) :
    ∃ g, IsLegalResponse G (position e edgeColours3) g (e i) ∧
      PartitionerWins G g (2 : Ordinal.{v}) :=
  checkedPlan_graph_reply G he (fun j => hmin (e j)) (fun _ h => Bool.noConfusion h)
    (fun x _ => hmin x) (fun _ _ h => h) (checked_edge3 i)

private theorem appendRow_edge3 (r : Fin 3 → Bool) :
    appendRow edge3 r = edge4 (r 0) (r 1) (r 2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem extends_edge4_initial : ∀ b : Bool,
    Extends (Fin.snoc edgeColours3 none) (initial4 b) := by
  simp only [Extends]
  decide +kernel

theorem edge_isolate_fresh_reply_of_missing_b_or_c {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (x : V) (hx : x ∉ Set.range e) (hbc : ¬ (G.Adj x (e 1) ∧ G.Adj x (e 2))) :
    ∃ g, IsLegalResponse G (position e edgeColours3) g x ∧
      PartitionerWins G g (2 : Ordinal.{v}) := by
  classical
  let r (i : Fin 3) := decide (G.Adj x (e i))
  have hr : ∀ i, r i = true ↔ G.Adj x (e i) := fun _ => decide_eq_true_iff
  have he4 := realizes_appendRow G he x hx r hr
  rw [appendRow_edge3] at he4
  have hbits : !(r 1 && r 2) = true := by
    cases hb : r 1 <;> cases hc : r 2 <;> simp
    exact hbc ⟨(hr 1).mp hb, (hr 2).mp hc⟩
  have hres := checkedPlan_graph_reply G he4
    (fun j => hmin (appendName e x hx j)) (fun _ h => Bool.noConfusion h)
    (fun w _ => hmin w) (extends_edge4_initial _)
    (checked_edge4 (r 0) (r 1) (r 2) hbits)
  simpa only [position_append_none, show (3 : Fin 4) = Fin.last 3 from rfl, appendName_last]
    using hres

theorem edge_isolate_fresh_reply_all_three_of_b_large_or_sealed {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (x : V) (hx : x ∉ Set.range e) (hrow : ∀ j, G.Adj x (e j))
    (hb : 4 ≤ #(G.neighborSet (e 1)) ∨ G.neighborSet (e 1) ⊆ insert x (Set.range e)) :
    ∃ g, IsLegalResponse G (position e edgeColours3) g x ∧
      PartitionerWins G g (2 : Ordinal.{v}) := by
  let e4 := appendName e x hx
  have he4 : Realizes G e4 abc4 := by
    simpa only [appendRow_edge3, abc4] using
      realizes_appendRow G he x hx (fun _ => true) (fun i => ⟨fun _ => hrow i, fun _ => rfl⟩)
  have hres : ∃ g, IsLegalResponse G (position e4 (Fin.snoc edgeColours3 none)) g (e4 3) ∧
      PartitionerWins G g (2 : Ordinal.{v}) := by
    rcases hb with hfour | hseal
    · have hlo (i : Fin 4) : ((![(2 : ℕ), 4, 2, 2] i : ℕ) : Cardinal) ≤
          #(G.neighborSet (e4 i)) := by
        fin_cases i
        · exact hmin _
        · exact hfour
        · exact hmin _
        · exact hmin _
      exact checkedPlan_graph_reply G he4 hlo (fun _ h => Bool.noConfusion h)
        (fun w _ => hmin w) (extends_edge4_initial true) checked_abc_b_ge4
    · have hs (i : Fin 4) (hi : bSealed4 i = true) :
          G.neighborSet (e4 i) ⊆ Set.range e4 := by
        fin_cases i <;> first | exact Bool.noConfusion hi | exact range_appendName e x hx ▸ hseal
      exact checkedPlan_graph_reply G he4 (fun j => hmin (e4 j)) hs
        (fun w _ => hmin w) (extends_edge4_initial true) checked_abc_b_degree2
  simpa only [e4, position_append_none, show (3 : Fin 4) = Fin.last 3 from rfl, appendName_last]
    using hres

private theorem appendRow_bcWitness (r : Fin 4 → Bool) (hr : r 2 = true) :
    appendRow (edge4 false true true) r = bcWitness (r 0) (r 1) (r 3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact hr

private theorem extends_bcColours :
    Extends (Fin.snoc (Fin.snoc edgeColours3 none) none) bcColours := by
  unfold Extends
  decide +kernel

theorem edge_isolate_fresh_reply_b_and_c_only {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (x : V) (hx : x ∉ Set.range e) (hxa : ¬ G.Adj x (e 0))
    (hxb : G.Adj x (e 1)) (hxc : G.Adj x (e 2)) :
    ∃ g, IsLegalResponse G (position e edgeColours3) g x ∧
      PartitionerWins G g (2 : Ordinal.{v}) := by
  classical
  let e4 := appendName e x hx
  have hr : ∀ i, (![false, true, true] : Fin 3 → Bool) i = true ↔ G.Adj x (e i) := by
    intro i
    fin_cases i
    · simpa using hxa
    · simpa using hxb
    · simpa using hxc
  have he4 : Realizes G e4 (edge4 false true true) := by
    simpa [appendRow_edge3] using realizes_appendRow G he x hx _ hr
  have hnamed : namedDegree (edge4 false true true) 2 = 1 := by decide
  obtain ⟨z, hcz, hz⟩ := (exists_freshNeighbor_iff G he4 2).mpr (by
    simpa only [hnamed, Nat.cast_one, one_add_one_eq_two] using hmin (e4 2))
  let r (i : Fin 4) := decide (G.Adj z (e4 i))
  have hrow : ∀ i, r i = true ↔ G.Adj z (e4 i) := fun _ => decide_eq_true_iff
  have he5 := realizes_appendRow G he4 z hz r hrow
  rw [appendRow_bcWitness r ((hrow 2).mpr hcz.symm)] at he5
  have hres := diagram_graph_reply G he5
    (fun i => hmin (appendName e4 z hz i)) (fun _ h => Bool.noConfusion h)
    (fun w _ => hmin w) extends_bcColours (checked_bc (r 0) (r 1) (r 3))
  change ∃ g, IsLegalResponse G (position (appendName e4 z hz)
    (Fin.snoc (Fin.snoc edgeColours3 none) none)) g ((appendName e4 z hz) (3 : Fin 4).castSucc) ∧
      PartitionerWins G g (2 : Ordinal.{v}) at hres
  simpa only [appendName_castSucc, position_append_none, e4,
    show (3 : Fin 4) = Fin.last 3 from rfl, appendName_last] using hres

/-- The named edge and isolate win at clock three if every all-three query leaves
the minority vertex sealed or that vertex has degree at least four. -/
theorem edge_isolate_wins_three_of_b_large_or_sealed {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hcase : ∀ x ∉ Set.range e, (∀ i, G.Adj x (e i)) →
      4 ≤ #(G.neighborSet (e 1)) ∨ G.neighborSet (e 1) ⊆ insert x (Set.range e)) :
    PartitionerWins G (position e edgeColours3) (3 : Ordinal.{v}) := by
  classical
  rw [PartitionerWins]
  intro x β hβ
  suffices h : ∃ g, IsLegalResponse G (position e edgeColours3) g x ∧
      PartitionerWins G g (2 : Ordinal.{v}) by
    obtain ⟨g, hg, hw⟩ := h
    have hle : β ≤ 2 := Order.lt_add_one_iff.mp
      (by simpa only [two_add_one_eq_three] using hβ)
    exact ⟨g, hg, _root_.Continuation.TC10.wins_mono G hle hw⟩
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    exact edge_isolate_named_reply G he hmin i
  · by_cases hbc : G.Adj x (e 1) ∧ G.Adj x (e 2)
    · by_cases ha : G.Adj x (e 0)
      · have ha3 (i : Fin 3) : G.Adj x (e i) := by
          fin_cases i
          · exact ha
          · exact hbc.1
          · exact hbc.2
        exact edge_isolate_fresh_reply_all_three_of_b_large_or_sealed G he hmin x hx ha3
          (hcase x hx ha3)
      · exact edge_isolate_fresh_reply_b_and_c_only G he hmin x hx ha hbc.1 hbc.2
    · exact edge_isolate_fresh_reply_of_missing_b_or_c G he hmin x hx hbc

end TenChallenges.Continuation.NamedPositions

namespace TenChallenges.Continuation.NamedPositions

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

private theorem appendRow_abc4 (r : Fin 4 → Bool) (hr : r 1 = true) :
    appendRow abc4 r = abc5 (r 0) (r 2) (r 3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact hr

private theorem namedDegree_abc5_b : ∀ ya yc yx : Bool, namedDegree (abc5 ya yc yx) 1 = 3 := by
  decide +kernel

/-- With an all-three query and a fourth neighbour excluded, naming an outside
neighbour of the minority vertex seals that vertex. -/
theorem extract_abc5 {e : Fin 3 ↪ V} (he : Realizes G e edge3)
    (x : V) (hx : x ∉ Set.range e) (hrow : ∀ i, G.Adj x (e i))
    (hsmall : ¬ 4 ≤ #(G.neighborSet (e 1)))
    (hunsealed : ¬ G.neighborSet (e 1) ⊆ Set.range (appendName e x hx)) :
    let e4 := appendName e x hx
    ∃ y : V, ∃ hy : y ∉ Set.range e4, ∃ ya yc yx : Bool,
      let e5 := appendName e4 y hy
      Realizes G e5 (abc5 ya yc yx) ∧ G.neighborSet (e 1) ⊆ Set.range e5 := by
  classical
  let e4 := appendName e x hx
  have he4 : Realizes G e4 abc4 := by
    have h := realizes_appendRow G he x hx (fun _ => true)
      (fun i => ⟨fun _ => hrow i, fun _ => rfl⟩)
    convert h using 1
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨y, hyb, hy⟩ := Set.not_subset.mp hunsealed
  let r (i : Fin 4) := decide (G.Adj y (e4 i))
  have hr : ∀ i, r i = true ↔ G.Adj y (e4 i) := fun _ => decide_eq_true_iff
  have hrb : r 1 = true := (hr 1).mpr (G.adj_symm hyb)
  have he5 := realizes_appendRow G he4 y hy r hr
  rw [appendRow_abc4 r hrb] at he5
  refine ⟨y, hy, r 0, r 2, r 3, he5, ?_⟩
  by_contra hmore
  obtain ⟨w, hbw, hw⟩ := Set.not_subset.mp hmore
  have hfour := add_one_le_degree_of_freshNeighbor G he5 1 (show G.Adj _ w from hbw) hw
  change _ ≤ #(G.neighborSet (e 1)) at hfour
  exact hsmall (by
    simpa only [namedDegree_abc5_b, Nat.cast_ofNat, three_add_one_eq_four] using hfour)

private def start5 : Colours 5 := Fin.snoc (Fin.snoc edgeColours3 none) none

private theorem extends_abc5 : Extends start5 (Fin.snoc (initial4 true) none) := by
  unfold Extends
  decide +kernel

private theorem extends_xyz : ∀ x y z : Option Bool,
    Extends (Fin.snoc start5 none) (xyzInitial x y z) := by
  simp only [Extends]
  decide +kernel

private theorem abc5_cases : ∀ ya yc yx : Bool,
    (!(ya && yc && !yx) = true) ∨ (ya = true ∧ yc = true ∧ yx = false) := by
  decide +kernel

/-- A five-name diagram leaves a legal reply and two more winning rounds,
unless the two additional named vertices are sealed cubic twins. -/
theorem abc5_reply_or_sealed_twins {e : Fin 5 ↪ V} {ya yc yx : Bool}
    (he : Realizes G e (abc5 ya yc yx))
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hb : G.neighborSet (e 1) ⊆ Set.range e) :
    (∃ g, IsLegalResponse G (position e start5) g (e 3) ∧
      PartitionerWins G g (2 : Ordinal.{v})) ∨
    (ya = true ∧ yc = true ∧ yx = false ∧
      G.neighborSet (e 3) ⊆ Set.range e ∧ G.neighborSet (e 4) ⊆ Set.range e) := by
  rcases abc5_cases ya yc yx with hordinary | ⟨rfl, rfl, rfl⟩
  · have hs (i : Fin 5) (hi : bSealed5 i = true) :
        G.neighborSet (e i) ⊆ Set.range e := by
      fin_cases i <;> first | exact Bool.noConfusion hi | exact hb
    exact Or.inl (checkedPlan_graph_reply G he (fun j => hmin (e j)) hs (fun w _ => hmin w)
      extends_abc5 (checked_abc_ordinary_y ya yc yx hordinary))
  · by_cases hy : G.neighborSet (e 4) ⊆ Set.range e
    · by_cases hx : G.neighborSet (e 3) ⊆ Set.range e
      · exact Or.inr ⟨rfl, rfl, rfl, hx, hy⟩
      · apply Or.inl
        obtain ⟨z, hxz, hz⟩ := Set.not_subset.mp hx
        classical
        let e6 := appendName e z hz
        let r (i : Fin 5) := decide (G.Adj z (e i))
        have hr : ∀ i, r i = true ↔ G.Adj z (e i) := fun _ => decide_eq_true_iff
        have hzb : r 1 = false :=
          decide_eq_false (fun ha : G.Adj z (e 1) => hz (hb ha.symm))
        have hzx : r 3 = true := (hr 3).mpr (G.adj_symm hxz)
        have hzy : r 4 = false :=
          decide_eq_false (fun ha : G.Adj z (e 4) => hz (hy ha.symm))
        have hre : r = ![r 0, false, r 2, true, false] := by
          funext i
          fin_cases i <;> first | rfl | exact hzb | exact hzx | exact hzy
        have he6 := realizes_appendRow G he z hz r hr
        rw [hre] at he6
        have hs (i : Fin 6) (hi : bySealed6 i = true) :
            G.neighborSet (e6 i) ⊆ Set.range e6 := by
          fin_cases i <;> first
            | exact Bool.noConfusion hi
            | exact hb.trans (by simp [e6])
            | exact hy.trans (by simp [e6])
        have hres := checkedPlan_graph_reply G he6 (fun i => hmin (e6 i)) hs
          (fun w _ => hmin w) (extends_xyz (some false) (some true) (some true))
          (checked_abc_extra_x_witness (r 0) (r 2))
        change ∃ g, IsLegalResponse G (position e6 (Fin.snoc start5 none)) g
          (e6 (3 : Fin 5).castSucc) ∧ PartitionerWins G g (2 : Ordinal.{v}) at hres
        simpa only [e6, position_append_none, appendName_castSucc] using hres
    · apply Or.inl
      obtain ⟨z, hyz, hz⟩ := Set.not_subset.mp hy
      classical
      let e6 := appendName e z hz
      let r (i : Fin 5) := decide (G.Adj z (e i))
      have hr : ∀ i, r i = true ↔ G.Adj z (e i) := fun _ => decide_eq_true_iff
      have hzb : r 1 = false :=
        decide_eq_false (fun ha : G.Adj z (e 1) => hz (hb ha.symm))
      have hzy : r 4 = true := (hr 4).mpr (G.adj_symm hyz)
      have hre : r = ![r 0, false, r 2, r 3, true] := by
        funext i
        fin_cases i <;> first | rfl | exact hzb | exact hzy
      have he6 := realizes_appendRow G he z hz r hr
      rw [hre] at he6
      have hs (i : Fin 6) (hi : bSealed6 i = true) :
          G.neighborSet (e6 i) ⊆ Set.range e6 := by
        fin_cases i <;> first
          | exact Bool.noConfusion hi
          | exact hb.trans (by simp [e6])
      have hres := checkedPlan_graph_reply G he6 (fun i => hmin (e6 i)) hs
        (fun w _ => hmin w) (extends_xyz (some true) none none)
        (checked_abc_extra_y_witness (r 0) (r 2) (r 3))
      change ∃ g, IsLegalResponse G (position e6 (Fin.snoc start5 none)) g
        (e6 (3 : Fin 5).castSucc) ∧ PartitionerWins G g (2 : Ordinal.{v}) at hres
      simpa only [e6, position_append_none, appendName_castSucc] using hres

/-- An all-three query and its unique remaining minority neighbour form
the obstruction precisely when both are sealed twins in their five-name diagram. -/
def HasCubicTwinObstruction (e : Fin 3 ↪ V) : Prop :=
  ∃ x : V, ∃ hx : x ∉ Set.range e,
    ∃ y : V, ∃ hy : y ∉ Set.range (appendName e x hx),
      let e5 := appendName (appendName e x hx) y hy
      Realizes G e5 abcTwin5 ∧ G.neighborSet (e5 1) ⊆ Set.range e5 ∧
        G.neighborSet (e5 3) ⊆ Set.range e5 ∧ G.neighborSet (e5 4) ⊆ Set.range e5

theorem edge_isolate_wins_three_or_cubic_twins {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G (position e edgeColours3) (3 : Ordinal.{v}) ∨
      HasCubicTwinObstruction G e := by
  classical
  by_cases hTwin : HasCubicTwinObstruction G e
  · exact Or.inr hTwin
  · apply Or.inl
    rw [PartitionerWins]
    intro x β hβ
    suffices h : ∃ g, IsLegalResponse G (position e edgeColours3) g x ∧
        PartitionerWins G g (2 : Ordinal.{v}) by
      obtain ⟨g, hg, hw⟩ := h
      have hle : β ≤ 2 := Order.lt_add_one_iff.mp
        (by simpa only [two_add_one_eq_three] using hβ)
      exact ⟨g, hg, _root_.Continuation.TC10.wins_mono G hle hw⟩
    by_cases hx : x ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hx
      exact edge_isolate_named_reply G he hmin i
    · by_cases hbc : G.Adj x (e 1) ∧ G.Adj x (e 2)
      · by_cases ha : G.Adj x (e 0)
        · have hrow (i : Fin 3) : G.Adj x (e i) := by
            fin_cases i
            · exact ha
            · exact hbc.1
            · exact hbc.2
          by_cases hb : 4 ≤ #(G.neighborSet (e 1)) ∨
              G.neighborSet (e 1) ⊆ insert x (Set.range e)
          · exact edge_isolate_fresh_reply_all_three_of_b_large_or_sealed G he hmin x hx hrow hb
          · obtain ⟨y, hy, ya, yc, yx, he5, hb5⟩ := extract_abc5 G he x hx hrow
              (fun h => hb (Or.inl h)) (fun h => hb (Or.inr (by simpa using h)))
            rcases abc5_reply_or_sealed_twins G he5 hmin hb5 with
              hresp | ⟨rfl, rfl, rfl, hsx, hsy⟩
            · simpa only [start5, position_append_none,
                show (3 : Fin 5) = (3 : Fin 4).castSucc from rfl,
                appendName_castSucc, show (3 : Fin 4) = Fin.last 3 from rfl,
                appendName_last] using hresp
            · exact (hTwin ⟨x, hx, y, hy, he5, hb5, hsx, hsy⟩).elim
        · exact edge_isolate_fresh_reply_b_and_c_only G he hmin x hx ha hbc.1 hbc.2
      · exact edge_isolate_fresh_reply_of_missing_b_or_c G he hmin x hx hbc

/-- For a sealed name the realized row lists every neighbour. -/
theorem sealed_neighborSet_eq_image_indices {n : ℕ} {e : Fin n ↪ V} {A : Edges n}
    (he : Realizes G e A) (i : Fin n) (hseal : G.neighborSet (e i) ⊆ Set.range e) :
    G.neighborSet (e i) = e '' {j | A i j = true} := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := hseal hx
    exact ⟨j, (he i j).mpr hx, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact (he i j).mp hj

private theorem abcTwin5_row1 : {j : Fin 5 | abcTwin5 1 j = true} = {0, 3, 4} := by
  ext j
  fin_cases j <;> decide

private theorem abcTwin5_row3 : {j : Fin 5 | abcTwin5 3 j = true} = {0, 1, 2} := by
  ext j
  fin_cases j <;> decide

private theorem abcTwin5_row4 : {j : Fin 5 | abcTwin5 4 j = true} = {0, 1, 2} := by
  ext j
  fin_cases j <;> decide

theorem cubic_twin_obstruction_neighborhoods {e : Fin 3 ↪ V}
    (h : HasCubicTwinObstruction G e) :
    ∃ x y : V, x ∉ Set.range e ∧ y ∉ Set.range e ∧ x ≠ y ∧
      G.neighborSet (e 1) = {e 0, x, y} ∧
      G.neighborSet x = {e 0, e 1, e 2} ∧ G.neighborSet y = {e 0, e 1, e 2} := by
  obtain ⟨x, hx, y, hy, he, hb, hxs, hys⟩ := h
  have hy' : y ∉ insert x (Set.range e) := by simpa using hy
  refine ⟨x, y, hx, fun h => hy' (Or.inr h), fun h => hy' (Or.inl h.symm), ?_, ?_, ?_⟩
  · have hn := sealed_neighborSet_eq_image_indices G he 1 hb
    rw [abcTwin5_row1, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at hn
    exact hn
  · have hn := sealed_neighborSet_eq_image_indices G he 3 hxs
    rw [abcTwin5_row3, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at hn
    exact hn
  · have hn := sealed_neighborSet_eq_image_indices G he 4 hys
    rw [abcTwin5_row4, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at hn
    exact hn

/-- The edge-and-isolate position wins three rounds unless its exact
neighbourhoods have the two cubic twins. -/
theorem edge_isolate_wins_three_or_neighborhoods {e : Fin 3 ↪ V}
    (he : Realizes G e edge3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G (position e edgeColours3) (3 : Ordinal.{v}) ∨
      ∃ x y : V, x ∉ Set.range e ∧ y ∉ Set.range e ∧ x ≠ y ∧
        G.neighborSet (e 1) = {e 0, x, y} ∧
        G.neighborSet x = {e 0, e 1, e 2} ∧ G.neighborSet y = {e 0, e 1, e 2} := by
  rcases edge_isolate_wins_three_or_cubic_twins G he hmin with hw | ht
  · exact Or.inl hw
  · exact Or.inr (cubic_twin_obstruction_neighborhoods G ht)

end TenChallenges.Continuation.NamedPositions

end

-- Source: Continuation/UnfriendlyColoredTriangle.lean
section

/-! # Three more rounds from a coloured triangle -/

set_option autoImplicit false

universe u v

section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TenChallenges.Continuation.NamedPositions.TriangleReplies
variable {n : ℕ}

def tri3 : Edges 3 := ![![false, true, true], ![true, false, true], ![true, true, false]]

def triStart : Colours 3 := ![some false, some false, some true]

def tri4 (xu xv xw : Bool) : Edges 4 :=
  ![![false, true, true, xu], ![true, false, true, xv],
    ![true, true, false, xw], ![xu, xv, xw, false]]

def tri4Touch : Edges 4 := tri4 true false true
def tri4Miss : Edges 4 := tri4 true false false

def tri5Touch (yv yw yx : Bool) : Edges 5 := appendRow tri4Touch ![true, yv, yw, yx]
def tri5Miss (yu yw yx : Bool) : Edges 5 := appendRow tri4Miss ![yu, true, yw, yx]
def tri5Exceptional : Edges 5 := tri5Miss false true true

def largeAt (i : Fin n) : Fin n → ℕ := fun j => if j = i then 4 else 2
def flags (s : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ s)

def triColours4 (x : Bool) : Colours 4 := ![some false, some false, some true, some x]

def triColours5 (x y : Option Bool) : Colours 5 := ![some false, some false, some true, x, y]

def triColours6 (x y z : Option Bool) : Colours 6 := ![some false, some false, some true, x, y, z]

theorem checked_tri3 : ∀ i : Fin 3,
    CheckedPlan tri3 (fun _ => 2) (flags ∅) 2 triStart i
      (singletonPlan tri3 (fun _ => 2) 2 triStart) := by
  decide +kernel

theorem checked_tri4_equal : ∀ b xw : Bool,
    let A := tri4 b b xw
    let p := triColours4 b
    CheckedPlan A (fun _ => 2) (flags ∅) 2 p 3 (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

theorem checked_tri_touch_large_u : ∀ yv yw yx : Bool,
    let A := tri5Touch yv yw yx
    let p := triColours5 (some false) none
    let lo : Fin 5 → ℕ := largeAt 0
    let extra (i : Fin 5) := if i = 0 then some (triColours5 (some false) (some true)) else none
    CheckedPlan A lo (flags ∅) 2 p 3 (singletonPlan A lo 2 p extra) := by
  decide +kernel

theorem checked_tri_touch_sealed_u_large_v :
    let p := triColours4 true
    let lo : Fin 4 → ℕ := largeAt 1
    CheckedPlan tri4Touch lo (flags {0}) 2 p 3 (singletonPlan tri4Touch lo 2 p) := by
  decide +kernel

theorem checked_tri_touch_sealed_uv :
    let p := triColours4 true
    CheckedPlan tri4Touch (fun _ => 2) (flags {0, 1}) 2 p 3
      (singletonPlan tri4Touch (fun _ => 2) 2 p) := by
  decide +kernel

theorem checked_tri_miss_large_v :
    let p := triColours4 true
    let lo : Fin 4 → ℕ := largeAt 1
    CheckedPlan tri4Miss lo (flags ∅) 2 p 3 (singletonPlan tri4Miss lo 2 p) := by
  decide +kernel

theorem checked_tri_miss_sealed_v :
    let p := triColours4 true
    CheckedPlan tri4Miss (fun _ => 2) (flags {1}) 2 p 3
      (singletonPlan tri4Miss (fun _ => 2) 2 p) := by
  decide +kernel

theorem checked_tri_miss_ordinary_y : ∀ yu yw yx : Bool, (!(!yu && yw && yx) = true) →
    let A := tri5Miss yu yw yx
    let p := triColours5 (some true) none
    CheckedPlan A (fun _ => 2) (flags {1}) 2 p 3 (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

theorem checked_tri_miss_extra_y : ∀ zu zw zx : Bool,
    let A := appendRow tri5Exceptional ![zu, false, zw, zx, true]
    let p := triColours6 (some true) none none
    let extra (i : Fin 6) :=
      if i = 4 then some (triColours6 (some true) (some true) (some false)) else none
    CheckedPlan A (fun _ => 2) (flags {1}) 2 p 3 (singletonPlan A (fun _ => 2) 2 p extra) := by
  decide +kernel

theorem checked_tri_miss_sealed_y_large_u : ∀ zw zx : Bool,
    let A := appendRow tri5Exceptional ![true, false, zw, zx, false]
    let p := triColours6 (some false) (some true) none
    let lo : Fin 6 → ℕ := largeAt 0
    let extra (i : Fin 6) :=
      if i = 0 then some (triColours6 (some false) (some true) (some true)) else none
    CheckedPlan A lo (flags {1, 4}) 2 p 3 (singletonPlan A lo 2 p extra) := by
  decide +kernel

end TenChallenges.Continuation.NamedPositions.TriangleReplies

end

namespace TenChallenges.Continuation.NamedPositions.TriangleReplies

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

abbrev ReplyTwo (f : V → Option Bool) (x : V) : Prop :=
  ∃ g, IsLegalResponse G f g x ∧ PartitionerWins G g (2 : Ordinal.{v})

def start4 : Colours 4 := Fin.snoc triStart none
def start5 : Colours 5 := Fin.snoc start4 none
def start6 : Colours 6 := Fin.snoc start5 none

theorem extends_start4 : ∀ b : Bool, Extends start4 (triColours4 b) := by
  simp only [Extends]
  decide +kernel

theorem extends_start5 : ∀ a b : Option Bool, Extends start5 (triColours5 a b) := by
  simp only [Extends]
  decide +kernel

theorem extends_start6 : ∀ a b c : Option Bool, Extends start6 (triColours6 a b c) := by
  simp only [Extends]
  decide +kernel

theorem reply_of_table {e : Fin n ↪ V} {A : Edges n} {lo : Fin n → ℕ} {s : Finset (Fin n)}
    {f p : Colours n} {i : Fin n} {plan : ReplyPlan n}
    (he : Realizes G e A) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hl : ∀ j, (lo j : Cardinal) ≤ #(G.neighborSet (e j)))
    (hs : ∀ j ∈ s, G.neighborSet (e j) ⊆ Set.range e)
    (hf : Extends f p) (hp : CheckedPlan A lo (flags s) 2 p i plan) :
    ReplyTwo.{u,v} G (position e f) (e i) :=
  checkedPlan_graph_reply G he hl (fun j hj => hs j (of_decide_eq_true hj))
    (fun w _ => hmin w) hf hp

theorem bounds_largeAt {e : Fin n ↪ V} (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (i : Fin n) (hi : 4 ≤ #(G.neighborSet (e i))) (j : Fin n) :
    (largeAt i j : Cardinal) ≤ #(G.neighborSet (e j)) := by
  by_cases h : j = i
  · subst j
    simpa [largeAt] using hi
  · simpa [largeAt, h] using hmin (e j)

theorem project_append_reply {e : Fin n ↪ V} {z : V} (hz : z ∉ Set.range e)
    (p : Colours n) (i : Fin n)
    (h : ReplyTwo.{u,v} G (position (appendName e z hz) (Fin.snoc p none))
      ((appendName e z hz) i.castSucc)) :
    ReplyTwo.{u,v} G (position e p) (e i) := by
  simpa only [position_append_none, appendName_castSucc] using h

theorem old_names_subset_append {e : Fin n ↪ V} {z : V} (hz : z ∉ Set.range e) :
    Set.range e ⊆ Set.range (appendName e z hz) := by
  rw [range_appendName]
  exact Set.subset_insert _ _

theorem sealed_of_small_degree {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A) (i : Fin n)
    (hsmall : ¬ (namedDegree A i : Cardinal) + 1 ≤ #(G.neighborSet (e i))) :
    G.neighborSet (e i) ⊆ Set.range e := by
  by_contra h
  exact hsmall ((exists_freshNeighbor_iff G he i).mp (Set.not_subset.mp h))

theorem triangle_named_reply {e : Fin 3 ↪ V}
    (he : Realizes G e tri3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) (i : Fin 3) :
    ReplyTwo.{u,v} G (position e triStart) (e i) :=
  reply_of_table G he hmin (fun j => hmin (e j)) (by simp) (fun _ _ h => h) (checked_tri3 i)

theorem triangle_equal_row_reply {e : Fin 4 ↪ V} {b xw : Bool}
    (he : Realizes G e (tri4 b b xw)) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    ReplyTwo.{u,v} G (position e start4) (e 3) :=
  reply_of_table G he hmin (fun j => hmin (e j)) (by simp) (extends_start4 b)
    (checked_tri4_equal b xw)

theorem exceptional_triangle_reply_or_cubic {e : Fin 5 ↪ V}
    (he : Realizes G e tri5Exceptional) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hv : G.neighborSet (e 1) ⊆ Set.range e) :
    ReplyTwo.{u,v} G (position e start5) (e 3) ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  classical
  by_cases hseal : G.neighborSet (e 4) ⊆ Set.range e
  · by_cases hu : 4 ≤ #(G.neighborSet (e 0))
    · apply Or.inl
      obtain ⟨z, huz, hz⟩ := exists_freshNeighbor_of_degree_four G he 0 (by decide) hu
      let e6 := appendName e z hz
      let r (i : Fin 5) := decide (G.Adj z (e i))
      have hr : ∀ i, r i = true ↔ G.Adj z (e i) := fun _ => decide_eq_true_iff
      have hzu : r 0 = true := (hr 0).mpr huz.symm
      have hzv : r 1 = false := decide_eq_false (fun h : G.Adj z (e 1) => hz (hv h.symm))
      have hzy : r 4 = false := decide_eq_false (fun h : G.Adj z (e 4) => hz (hseal h.symm))
      have hr' : r = ![true, false, r 2, r 3, false] := by
        funext i
        fin_cases i <;> first | rfl | exact hzu | exact hzv | exact hzy
      have he6 := realizes_appendRow G he z hz r hr
      rw [hr'] at he6
      have hs (i : Fin 6) (hi : i ∈ ({1, 4} : Finset (Fin 6))) :
          G.neighborSet (e6 i) ⊆ Set.range e6 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hv.trans (old_names_subset_append hz)
        · exact hseal.trans (old_names_subset_append hz)
      exact project_append_reply G hz start5 3
        (reply_of_table G he6 hmin (bounds_largeAt G (e := e6) hmin 0 hu) hs
          (extends_start6 (some false) (some true) none)
          (checked_tri_miss_sealed_y_large_u (r 2) (r 3)))
    · have hnamedU : namedDegree tri5Exceptional 0 = 3 := by decide
      have hnamedV : namedDegree tri5Exceptional 1 = 3 := by decide
      have hsu := sealed_of_small_degree G he 0 (by
        simpa only [hnamedU, Nat.cast_ofNat, three_add_one_eq_four] using hu)
      exact Or.inr ⟨by simpa only [hnamedU, Nat.cast_ofNat] using degree_eq_namedDegree G he 0 hsu,
        by simpa only [hnamedV, Nat.cast_ofNat] using degree_eq_namedDegree G he 1 hv⟩
  · apply Or.inl
    obtain ⟨z, hyz, hz⟩ := Set.not_subset.mp hseal
    let e6 := appendName e z hz
    let r (i : Fin 5) := decide (G.Adj z (e i))
    have hr : ∀ i, r i = true ↔ G.Adj z (e i) := fun _ => decide_eq_true_iff
    have hzv : r 1 = false := decide_eq_false (fun h : G.Adj z (e 1) => hz (hv h.symm))
    have hzy : r 4 = true := (hr 4).mpr (G.adj_symm hyz)
    have hr' : r = ![r 0, false, r 2, r 3, true] := by
      funext i
      fin_cases i <;> first | rfl | exact hzv | exact hzy
    have he6 := realizes_appendRow G he z hz r hr
    rw [hr'] at he6
    have hs (i : Fin 6) (hi : i ∈ ({1} : Finset (Fin 6))) :
        G.neighborSet (e6 i) ⊆ Set.range e6 := by
      simp only [Finset.mem_singleton] at hi
      subst i
      exact hv.trans (old_names_subset_append hz)
    exact project_append_reply G hz start5 3
      (reply_of_table G he6 hmin (fun j => hmin (e6 j)) hs
        (extends_start6 (some true) none none) (checked_tri_miss_extra_y (r 0) (r 2) (r 3)))

private theorem appendRow_tri4Miss (r : Fin 4 → Bool) (hr : r 1 = true) :
    appendRow tri4Miss r = tri5Miss (r 0) (r 2) (r 3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact hr

private theorem tri5Miss_namedDegree_v : ∀ yu yw yx : Bool,
    namedDegree (tri5Miss yu yw yx) 1 = 3 := by decide

private theorem tri5Miss_cases : ∀ yu yw yx : Bool,
    (!(!yu && yw && yx) = true) ∨ (yu = false ∧ yw = true ∧ yx = true) := by decide

theorem triangle_miss_reply_or_cubic {e : Fin 4 ↪ V}
    (he : Realizes G e tri4Miss) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    ReplyTwo.{u,v} G (position e start4) (e 3) ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  classical
  by_cases hfour : 4 ≤ #(G.neighborSet (e 1))
  · exact Or.inl (reply_of_table G he hmin (bounds_largeAt G (e := e) hmin 1 hfour)
      (by simp) (extends_start4 true) checked_tri_miss_large_v)
  · by_cases hseal : G.neighborSet (e 1) ⊆ Set.range e
    · have hs (i : Fin 4) (hi : i ∈ ({1} : Finset (Fin 4))) :
          G.neighborSet (e i) ⊆ Set.range e := by
        simp only [Finset.mem_singleton] at hi
        exact hi.symm ▸ hseal
      exact Or.inl (reply_of_table G he hmin (fun j => hmin (e j)) hs
        (extends_start4 true) checked_tri_miss_sealed_v)
    · obtain ⟨y, hvy, hy⟩ := Set.not_subset.mp hseal
      let e5 := appendName e y hy
      let r (i : Fin 4) := decide (G.Adj y (e i))
      have hr : ∀ i, r i = true ↔ G.Adj y (e i) := fun _ => decide_eq_true_iff
      have he5 := realizes_appendRow G he y hy r hr
      rw [appendRow_tri4Miss r ((hr 1).mpr (G.adj_symm hvy))] at he5
      have hv5 : G.neighborSet (e5 1) ⊆ Set.range e5 := sealed_of_small_degree G he5 1 (by
        change ¬ (namedDegree (tri5Miss (r 0) (r 2) (r 3)) 1 : Cardinal) + 1 ≤
          #(G.neighborSet (e 1))
        simpa only [tri5Miss_namedDegree_v, Nat.cast_ofNat, three_add_one_eq_four] using hfour)
      rcases tri5Miss_cases (r 0) (r 2) (r 3) with hd | ⟨h0, h2, h3⟩
      · have hs (i : Fin 5) (hi : i ∈ ({1} : Finset (Fin 5))) :
            G.neighborSet (e5 i) ⊆ Set.range e5 := by
          simp only [Finset.mem_singleton] at hi
          exact hi.symm ▸ hv5
        exact Or.inl (project_append_reply G hy start4 3
          (reply_of_table G he5 hmin (fun j => hmin (e5 j)) hs
            (extends_start5 (some true) none) (checked_tri_miss_ordinary_y _ _ _ hd)))
      · have he5' : Realizes G e5 tri5Exceptional := by
          simpa only [h0, h2, h3, tri5Exceptional] using he5
        rcases exceptional_triangle_reply_or_cubic G he5' hmin hv5 with hreply | hcubic
        · exact Or.inl (project_append_reply G hy start4 3 hreply)
        · exact Or.inr hcubic

private theorem appendRow_tri4Touch (r : Fin 4 → Bool) (hr : r 0 = true) :
    appendRow tri4Touch r = tri5Touch (r 1) (r 2) (r 3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact hr

theorem triangle_touch_reply_or_cubic {e : Fin 4 ↪ V}
    (he : Realizes G e tri4Touch) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    ReplyTwo.{u,v} G (position e start4) (e 3) ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  classical
  have hnu : namedDegree tri4Touch 0 = 3 := by decide
  by_cases hu : 4 ≤ #(G.neighborSet (e 0))
  · obtain ⟨y, huy, hy⟩ := exists_freshNeighbor_of_degree_four G he 0 hnu hu
    let e5 := appendName e y hy
    let r (i : Fin 4) := decide (G.Adj y (e i))
    have hr : ∀ i, r i = true ↔ G.Adj y (e i) := fun _ => decide_eq_true_iff
    have he5 := realizes_appendRow G he y hy r hr
    rw [appendRow_tri4Touch r ((hr 0).mpr huy.symm)] at he5
    exact Or.inl (project_append_reply G hy start4 3
      (reply_of_table G he5 hmin (bounds_largeAt G (e := e5) hmin 0 hu)
        (by simp) (extends_start5 (some false) none)
        (checked_tri_touch_large_u (r 1) (r 2) (r 3))))
  · have hsu : G.neighborSet (e 0) ⊆ Set.range e := sealed_of_small_degree G he 0 (by
        simpa only [hnu, Nat.cast_ofNat, three_add_one_eq_four] using hu)
    by_cases hv : 4 ≤ #(G.neighborSet (e 1))
    · have hs (i : Fin 4) (hi : i ∈ ({0} : Finset (Fin 4))) :
          G.neighborSet (e i) ⊆ Set.range e := by
        simp only [Finset.mem_singleton] at hi
        exact hi.symm ▸ hsu
      exact Or.inl (reply_of_table G he hmin (bounds_largeAt G (e := e) hmin 1 hv) hs
        (extends_start4 true) checked_tri_touch_sealed_u_large_v)
    · by_cases hsv : G.neighborSet (e 1) ⊆ Set.range e
      · have hs (i : Fin 4) (hi : i ∈ ({0, 1} : Finset (Fin 4))) :
            G.neighborSet (e i) ⊆ Set.range e := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hsu
          · exact hsv
        exact Or.inl (reply_of_table G he hmin (fun j => hmin (e j)) hs
          (extends_start4 true) checked_tri_touch_sealed_uv)
      · have hnv : namedDegree tri4Touch 1 = 2 := by decide
        have hge := (exists_freshNeighbor_iff G he 1).mp (Set.not_subset.mp hsv)
        have hvge : 3 ≤ #(G.neighborSet (e 1)) := by
          simpa only [hnv, Nat.cast_ofNat, two_add_one_eq_three] using hge
        have hvle : #(G.neighborSet (e 1)) ≤ 3 := Cardinal.lt_natCast_add_one_iff.mp (by
          simpa only [Nat.cast_ofNat, three_add_one_eq_four] using lt_of_not_ge hv)
        exact Or.inr ⟨by simpa only [hnu, Nat.cast_ofNat] using degree_eq_namedDegree G he 0 hsu,
          le_antisymm hvle hvge⟩

end TenChallenges.Continuation.NamedPositions.TriangleReplies

namespace TenChallenges.Continuation.NamedPositions.TriangleReplies

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

private theorem appendRow_tri3 (r : Fin 3 → Bool) :
    appendRow tri3 r = tri4 (r 0) (r 1) (r 2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem project_last_reply {e : Fin 3 ↪ V} {x : V} (hx : x ∉ Set.range e)
    (h : ReplyTwo.{u,v} G (position (appendName e x hx) start4)
      ((appendName e x hx) 3)) :
    ReplyTwo.{u,v} G (position e triStart) x := by
  simpa only [start4, position_append_none, show (3 : Fin 4) = Fin.last 3 from rfl,
    appendName_last] using h

/-- Orient a fresh query so one meeting just one matching vertex meets the first. -/
theorem triangle_oriented_reply_or_cubic {e : Fin 3 ↪ V}
    (he : Realizes G e tri3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (x : V) (hx : x ∉ Set.range e) (hdir : G.Adj x (e 1) → G.Adj x (e 0)) :
    ReplyTwo.{u,v} G (position e triStart) x ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  classical
  let r (i : Fin 3) := decide (G.Adj x (e i))
  have hr : ∀ i, r i = true ↔ G.Adj x (e i) := fun _ => decide_eq_true_iff
  have he4 := realizes_appendRow G he x hx r hr
  rw [appendRow_tri3] at he4
  have hord : r 1 = true → r 0 = true := fun h => (hr 0).mpr (hdir ((hr 1).mp h))
  have hcases : r 0 = r 1 ∨ (r 0 = true ∧ r 1 = false) := by
    cases h0 : r 0 <;> cases h1 : r 1 <;> simp_all
  rcases hcases with h | ⟨h0, h1⟩
  · rw [← h] at he4
    exact Or.inl (project_last_reply G hx (triangle_equal_row_reply G he4 hmin))
  · rw [h0, h1] at he4
    cases h2 : r 2
    · have hem : Realizes G (appendName e x hx) tri4Miss := by
        simpa only [h2, tri4Miss] using he4
      rcases triangle_miss_reply_or_cubic G hem hmin with h | h
      · exact Or.inl (project_last_reply G hx h)
      · exact Or.inr h
    · have het : Realizes G (appendName e x hx) tri4Touch := by
        simpa only [h2, tri4Touch] using he4
      rcases triangle_touch_reply_or_cubic G het hmin with h | h
      · exact Or.inl (project_last_reply G hx h)
      · exact Or.inr h

private def flipIndex : Fin 3 ≃ Fin 3 where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def flipNames (e : Fin 3 ↪ V) : Fin 3 ↪ V :=
  ⟨fun i => e (flipIndex i), e.injective.comp flipIndex.injective⟩

private theorem tri3_flip : ∀ i j, tri3 i j = tri3 (flipIndex i) (flipIndex j) := by
  decide +kernel

private theorem triStart_flip : ∀ i, triStart i = triStart (flipIndex i) := by
  decide +kernel

private theorem range_flipNames (e : Fin 3 ↪ V) : Set.range (flipNames e) = Set.range e := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨flipIndex i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨flipIndex.symm i, congrArg e (flipIndex.apply_symm_apply i)⟩

private theorem realizes_flipNames {e : Fin 3 ↪ V} (he : Realizes G e tri3) :
    Realizes G (flipNames e) tri3 := by
  intro i j
  rw [tri3_flip i j]
  exact he (flipIndex i) (flipIndex j)

private theorem position_flipNames (e : Fin 3 ↪ V) :
    position (flipNames e) triStart = position e triStart := by
  funext x
  by_cases hx : x ∈ Set.range (flipNames e)
  · obtain ⟨i, rfl⟩ := hx
    rw [position_name]
    change triStart i = position e triStart (e (flipIndex i))
    rw [position_name]
    exact triStart_flip i
  · exact (position_outside triStart hx).trans (position_outside triStart
      (by simpa only [range_flipNames] using hx)).symm

theorem triangle_fresh_reply_or_cubic {e : Fin 3 ↪ V}
    (he : Realizes G e tri3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (x : V) (hx : x ∉ Set.range e) :
    ReplyTwo.{u,v} G (position e triStart) x ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  by_cases hdir : G.Adj x (e 1) → G.Adj x (e 0)
  · exact triangle_oriented_reply_or_cubic G he hmin x hx hdir
  · have hno : ¬ G.Adj x (e 0) := fun h => hdir (fun _ => h)
    have hx' : x ∉ Set.range (flipNames e) := by rwa [range_flipNames]
    rcases triangle_oriented_reply_or_cubic G (realizes_flipNames G he) hmin x hx'
      (fun h => (hno h).elim) with h | h
    · exact Or.inl (by simpa only [position_flipNames] using h)
    · exact Or.inr ⟨h.2, h.1⟩

/-- The matching-colour ends of a triangle must both be cubic for a clock-three loss. -/
theorem colored_triangle_wins_three_or_both_cubic {e : Fin 3 ↪ V}
    (he : Realizes G e tri3) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G (position e triStart) (3 : Ordinal.{v}) ∨
      (#(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3) := by
  classical
  by_cases hcubic : #(G.neighborSet (e 0)) = 3 ∧ #(G.neighborSet (e 1)) = 3
  · exact Or.inr hcubic
  · apply Or.inl
    rw [PartitionerWins]
    intro x β hβ
    suffices h : ReplyTwo.{u,v} G (position e triStart) x by
      obtain ⟨g, hg, hw⟩ := h
      have hle : β ≤ 2 := Order.lt_add_one_iff.mp
        (by simpa only [two_add_one_eq_three] using hβ)
      exact ⟨g, hg, _root_.Continuation.TC10.wins_mono G hle hw⟩
    by_cases hx : x ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hx
      exact triangle_named_reply G he hmin i
    · rcases triangle_fresh_reply_or_cubic G he hmin x hx with h | h
      · exact h
      · exact (hcubic h).elim

end TenChallenges.Continuation.NamedPositions.TriangleReplies

end

-- Source: Continuation/UnfriendlyExposedBoundary.lean
section

universe u v

namespace Continuation.TC10R6

open TC10

variable {V : Type u} (G : SimpleGraph V)

/-- Relative to an earlier position, all its opposite-coloured vertices are sealed. -/
def SealedColour (f : V → Option Bool) (b : Bool) : Prop :=
  ∀ x, f x = none → ∀ y, f y = some (!b) → ¬ G.Adj x y

private lemma fresh_of_extends {f g : V → Option Bool} (hfg : Extends f g)
    {x : V} (hx : g x = none) : f x = none := by
  cases h : f x with
  | none => rfl
  | some c => simpa [hx] using hfg x c h

private lemma extra_same_subset {f g : V → Option Bool} {x : V} {b : Bool}
    (hfg : Extends f g) (hseal : SealedColour G f b) (hx : f x = none) :
    G.neighborSet x ∩ g ⁻¹' {some (!b)} ⊆ {y | f y = none ∧ g y = some (!b)} := by
  intro y hy
  refine ⟨?_, hy.2⟩
  cases h : f y with
  | none => rfl
  | some c =>
    exact (hseal x hx y ((Option.some.inj ((hfg y c h).symm.trans hy.2)) ▸ h) hy.1).elim

open Classical in
private lemma exposed_update_stable {f g : V → Option Bool} {b d : Bool} {x : V}
    (hfg : Extends f g) (hs : Stable G g) (hseal : SealedColour G f b)
    (hone : ({y | f y = none ∧ g y = some (!b)} : Set V).Subsingleton)
    (hopp : ∀ y, f y = none → g y = some (!b) → ∃ z, G.Adj y z ∧ g z = some b)
    (hx : g x = none)
    (hnew : UnfriendlyAt G (Function.update g x (some d)) x)
    (hkeep : ∀ y, g y = some b → d ≠ b ∨ ¬ G.Adj y x) :
    Stable G (Function.update g x (some d)) := by
  classical
  intro y c hy
  rcases eq_or_ne y x with rfl | hyx
  · exact hnew
  · have hyold : g y = some c := by simpa only [Function.update_of_ne hyx] using hy
    rcases Bool.eq_or_eq_not c b with rfl | rfl
    · exact TC10R5Helpers.unfriendly_update_of_color_or_nonadj G hx hyold
        (hs y _ hyold) (hkeep y hyold)
    · by_cases hyf : f y = none
      · refine unique_same G (!b) hy ?_ ?_
        · refine (Set.subsingleton_singleton (a := x)).anti ?_
          intro z hz
          by_contra hzx
          exact G.ne_of_adj hz.1 (hone ⟨hyf, hyold⟩ (extra_same_subset G hfg hseal hyf
            ⟨hz.1, by simpa only [Set.mem_preimage, Set.mem_singleton_iff,
              Function.update_of_ne (show z ≠ x from hzx)] using hz.2⟩))
        · obtain ⟨z, hyz, hz⟩ := hopp y hyf hyold
          exact ⟨z, hyz, by simpa only [Bool.not_not] using update_extends hx d z b hz⟩
      · exact TC10R5Helpers.unfriendly_update_of_color_or_nonadj G hx hyold
          (hs y (!b) hyold) (Or.inr (fun hyx' => hyf
            (extra_same_subset G hfg hseal (fresh_of_extends hfg hx) ⟨hyx'.symm, hyold⟩).1))

open Classical in
private lemma exposed_update {f g : V → Option Bool} {b : Bool} {x : V}
    (hfg : Extends f g) (hs : Stable G g) (hseal : SealedColour G f b)
    (hone : ({y | f y = none ∧ g y = some (!b)} : Set V).Subsingleton)
    (hopp : ∀ y, f y = none → g y = some (!b) → ∃ z, G.Adj y z ∧ g z = some b)
    (hx : g x = none) :
    ∃ d, Stable G (Function.update g x (some d)) ∧
      (d = !b → ∃ z, G.Adj x z ∧ g z = some b) := by
  by_cases hnb : ∃ z, G.Adj x z ∧ g z = some b
  · refine ⟨!b, exposed_update_stable G hfg hs hseal hone hopp hx ?_
        (fun _ _ => Or.inl (Bool.not_ne_self b)), fun _ => hnb⟩
    refine unique_same G (!b) (by simp) (hone.anti ?_) ?_
    · exact fun z hz => extra_same_subset G hfg hseal (fresh_of_extends hfg hx)
        ⟨hz.1, by simpa only [Set.mem_preimage, Set.mem_singleton_iff,
          Function.update_of_ne (G.ne_of_adj hz.1).symm] using hz.2⟩
    · obtain ⟨z, hxz, hz⟩ := hnb
      exact ⟨z, hxz, by simpa only [Bool.not_not] using update_extends hx (!b) z b hz⟩
  · exact ⟨b, exposed_update_stable G hfg hs hseal hone hopp hx
      (no_same G b (by simp) (fun z hxz hz => hnb
        ⟨z, hxz, by simpa only [Function.update_of_ne (G.ne_of_adj hxz).symm] using hz⟩))
      (fun y hy => Or.inr (fun hyx => hnb ⟨y, hyx.symm, hy⟩)),
      fun hd => (Bool.not_ne_self b hd.symm).elim⟩

private lemma wins_succ_of_responses {α : Ordinal.{v}} {f : V → Option Bool}
    (h : ∀ x, ∃ g, IsLegalResponse G f g x ∧ PartitionerWins G g α) :
    PartitionerWins G f (Order.succ α) := by
  rw [PartitionerWins]
  intro x β hβ
  obtain ⟨g, hg, hw⟩ := h x
  exact ⟨g, hg, wins_mono G (Order.lt_succ_iff.mp hβ) hw⟩

private lemma exposed_wins_two {f g : V → Option Bool} {b : Bool}
    (hfg : Extends f g) (hf : HasFiniteDomain g) (hs : Stable G g)
    (hseal : SealedColour G f b)
    (hone : ({y | f y = none ∧ g y = some (!b)} : Set V).Subsingleton)
    (hopp : ∀ y, f y = none → g y = some (!b) → ∃ z, G.Adj y z ∧ g z = some b) :
    PartitionerWins G g (2 : Ordinal.{v}) := by
  classical
  rw [← one_add_one_eq_two, ← Order.succ_eq_add_one]
  apply wins_succ_of_responses G
  intro x
  by_cases hx : g x = none
  · obtain ⟨d, hd, _⟩ := exposed_update G hfg hs hseal hone hopp hx
    exact ⟨_, ⟨update_extends hx d, finite_update hf x d, hd x d (by simp)⟩,
      stable_wins_one G (finite_update hf x d) hd⟩
  · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨g, ⟨fun _ _ h => h, hf, hs x d hd⟩, stable_wins_one G hf hs⟩

/-- A stable partial colouring with a monochromatic exposed boundary wins at clock three. -/
theorem exposed_wins_three {f : V → Option Bool} {b : Bool}
    (hf : HasFiniteDomain f) (hs : Stable G f) (hseal : SealedColour G f b) :
    PartitionerWins G f (3 : Ordinal.{v}) := by
  classical
  rw [← two_add_one_eq_three, ← Order.succ_eq_add_one]
  apply wins_succ_of_responses G
  have hnone (y : V) (hy : f y = none) (hy' : f y = some (!b)) : False := by
    simp [hy] at hy'
  have he : ({y | f y = none ∧ f y = some (!b)} : Set V).Subsingleton :=
    fun _ hy _ _ => (hnone _ hy.1 hy.2).elim
  have ho : ∀ y, f y = none → f y = some (!b) → ∃ z, G.Adj y z ∧ f z = some b :=
    fun _ hy hy' => (hnone _ hy hy').elim
  intro x
  by_cases hx : f x = none
  · obtain ⟨d, hd, hdo⟩ := exposed_update G (fun _ _ h => h) hs hseal he ho hx
    have hsubset :
        {y | f y = none ∧ Function.update f x (some d) y = some (!b)} ⊆ ({x} : Set V) := by
      intro y hy
      by_contra hyx
      exact hnone y hy.1 (by simpa only [Function.update_of_ne (show y ≠ x from hyx)] using hy.2)
    refine ⟨_, ⟨update_extends hx d, finite_update hf x d, hd x d (by simp)⟩,
      exposed_wins_two G (update_extends hx d) (finite_update hf x d) hd hseal
        ((Set.subsingleton_singleton (a := x)).anti hsubset) ?_⟩
    · intro y hy hy'
      obtain rfl : y = x := hsubset ⟨hy, hy'⟩
      obtain ⟨z, hyz, hz⟩ := hdo (Option.some.inj (by simpa only [Function.update_self] using hy'))
      exact ⟨z, hyz, update_extends hx d z b hz⟩
  · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨f, ⟨fun _ _ h => h, hf, hs x d hd⟩,
      exposed_wins_two G (fun _ _ h => h) hf hs hseal he ho⟩

end Continuation.TC10R6

end

-- Source: Continuation/UnfriendlyNonadjacentPair.lean
section

/-! # Four rounds from a nonadjacent monochromatic pair -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.NamedPositions

open _root_.Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The vertices named zero and two are assigned; the third query is name one. -/
def beforeEdgeIsolate : Colours 3 := ![some false, none, some false]

private def twinAlternate : Colours 5 :=
  ![some false, some false, some false, some true, some true]

private theorem twinAlternate_balanced : ∀ i : Fin 5, Balanced abcTwin5 twinAlternate i := by
  decide +kernel

private theorem twinAlternate_true :
    ∀ i : Fin 5, twinAlternate i = some true → i = 3 ∨ i = 4 := by decide

private theorem twinAlternate_assigned : ∀ i : Fin 5, twinAlternate i ≠ none := by decide

private theorem extends_twinAlternate :
    Extends (Fin.snoc (Fin.snoc beforeEdgeIsolate none) none) twinAlternate := by
  unfold Extends
  decide +kernel

private theorem position_extends {n : ℕ} (e : Fin n ↪ V) {p q : Colours n}
    (hpq : Extends p q) : Extends (position e p) (position e q) := by
  intro w d hw
  by_cases hn : w ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    simpa only [position_name] using hpq i d ((position_name e p i).symm.trans hw)
  · simp [position_outside p hn] at hw

private theorem position_stable {n : ℕ} {e : Fin n ↪ V} {A : Edges n} {p : Colours n}
    (he : Realizes G e A) (h : ∀ i, Balanced A p i) : Stable G (position e p) := by
  intro w d hw
  have hwname : w ∈ Set.range e := Classical.byContradiction fun hn =>
    Option.some_ne_none d (hw.symm.trans (position_outside p hn))
  obtain ⟨i, rfl⟩ := hwname
  obtain ⟨c, hc, hbal⟩ := h i
  exact ⟨c, (position_name e p i).trans hc,
    by simpa only [count_eq G he, Nat.cast_le] using hbal⟩

/-- A cubic-twin obstruction is answered by colouring the query false and the
two twins true. The resulting exposed boundary is monochromatic. -/
theorem cubic_twins_alternate_reply {e : Fin 3 ↪ V}
    (ht : HasCubicTwinObstruction G e) :
    ∃ g, IsLegalResponse G (position e beforeEdgeIsolate) g (e 1) ∧
      PartitionerWins G g (3 : Ordinal.{v}) := by
  obtain ⟨x, hx, y, hy, he, _, hsx, hsy⟩ := ht
  let e5 := appendName (appendName e x hx) y hy
  let g := position e5 twinAlternate
  have hExt : Extends (position e beforeEdgeIsolate) g := by
    simpa only [e5, position_append_none] using position_extends e5 extends_twinAlternate
  have he1 : e5 1 = e 1 := by
    simp only [e5, show (1 : Fin 5) = (1 : Fin 4).castSucc from rfl,
      appendName_castSucc, show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl]
  have hstable : Stable G g := position_stable G he twinAlternate_balanced
  have hseal : _root_.Continuation.TC10R6.SealedColour G g false := by
    intro w hw z hz hadj
    exact
      let hzname : z ∈ Set.range e5 := Classical.byContradiction fun hn =>
        Option.some_ne_none true (hz.symm.trans (position_outside twinAlternate hn))
      let ⟨i, hi⟩ := hzname
      let hz' : g (e5 i) = some true := hi.symm ▸ hz
      let hAdj : G.Adj (e5 i) w := hi.symm ▸ hadj.symm
      let hwname : w ∈ Set.range e5 :=
        (twinAlternate_true i ((position_name e5 twinAlternate i).symm.trans hz')).elim
          (fun h => hsx (show G.Adj (e5 3) w from h ▸ hAdj))
          (fun h => hsy (show G.Adj (e5 4) w from h ▸ hAdj))
      let ⟨j, hj⟩ := hwname
      let hw' : g (e5 j) = none := hj.symm ▸ hw
      twinAlternate_assigned j ((position_name e5 twinAlternate j).symm.trans hw')
  exact ⟨g, ⟨hExt, position_finite e5 twinAlternate,
    hstable (e 1) false (he1 ▸ position_name e5 twinAlternate 1)⟩,
    _root_.Continuation.TC10R6.exposed_wins_three G (position_finite e5 twinAlternate) hstable hseal⟩

def triple (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fin 3 ↪ V :=
  ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

private theorem position_of_values {n : ℕ} (f : V → Option Bool)
    (e : Fin n ↪ V) (p : Colours n) (hf : ∀ i, f (e i) = p i)
    (hcover : ∀ x, f x ≠ none → x ∈ Set.range e) : f = position e p := by
  classical
  funext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    exact (hf i).trans (position_name e p i).symm
  · have hn : f x = none := Classical.byContradiction fun hn => hx (hcover x hn)
    exact hn.trans (position_outside p hx).symm

private theorem one_edge_third_reply {f : V → Option Bool} {a b c : V}
    (ha : f a = some false) (hb : f b = none) (hc : f c = some false)
    (hcover : ∀ x, f x ≠ none → x = a ∨ x = c) (hac : a ≠ c)
    (hnac : ¬ G.Adj a c) (hba : G.Adj b a) (hnbc : ¬ G.Adj b c)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    ∃ g, IsLegalResponse G f g b ∧ PartitionerWins G g (3 : Ordinal.{v}) := by
  have hbc : b ≠ c := fun h => Option.some_ne_none false (hc.symm.trans (h ▸ hb))
  let e := triple a b c (G.ne_of_adj hba).symm hac hbc
  have hf : f = position e beforeEdgeIsolate :=
    position_of_values f e beforeEdgeIsolate
      (fun i => by fin_cases i <;> first | exact ha | exact hb | exact hc)
      (fun x hx => (hcover x hx).elim
        (fun h => ⟨0, h.symm⟩) (fun h => ⟨2, h.symm⟩))
  have he : Realizes G e edge3 := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact ⟨fun _ => hba, fun _ => rfl⟩
      | exact ⟨fun _ => hba.symm, fun _ => rfl⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (G.irrefl h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hnac h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hnac h.symm).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hnbc h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hnbc h.symm).elim⟩
  rw [hf]
  change ∃ g, IsLegalResponse G (position e beforeEdgeIsolate) g (e 1) ∧
    PartitionerWins G g (3 : Ordinal.{v})
  rcases edge_isolate_wins_three_or_cubic_twins G he hmin with hw | ht
  · have hExt : Extends beforeEdgeIsolate edgeColours3 := by
      unfold Extends
      decide
    have hbal : ∀ i : Fin 3, Balanced edge3 edgeColours3 i := by decide
    exact ⟨position e edgeColours3, ⟨position_extends e hExt, position_finite _ _,
      position_stable G he hbal _ true (position_name _ _ _)⟩, hw⟩
  · exact cubic_twins_alternate_reply G ht

private theorem mono_ready {f : V → Option Bool}
    (hc : ∀ x, f x ≠ none → f x = some false)
    (hi : ∀ x y, f x ≠ none → f y ≠ none → ¬ G.Adj x y) : Ready G f :=
  Or.inl ⟨fun x d hd => Option.some.inj (hd.symm.trans (hc x (hd ▸ Option.some_ne_none d))),
    fun x y hx hy => hi x y (hx ▸ Option.some_ne_none false) (hy ▸ Option.some_ne_none false)⟩

private theorem independent_fresh_reply {f : V → Option Bool} {b : V}
    (hf : HasFiniteDomain f) (hb : f b = none)
    (hc : ∀ x, f x ≠ none → f x = some false)
    (hi : ∀ x y, f x ≠ none → f y ≠ none → ¬ G.Adj x y)
    (hnew : ∀ x, f x ≠ none → ¬ G.Adj b x) :
    ∃ g, IsLegalResponse G f g b ∧ PartitionerWins G g (3 : Ordinal.{v}) := by
  classical
  let g := Function.update f b (some false)
  have hold (x : V) (hx : x ≠ b) (hg : g x ≠ none) : f x ≠ none := by
    simpa only [g, Function.update_of_ne hx] using hg
  have hmono : ∀ x, g x ≠ none → g x = some false := by
    intro x hx
    rcases eq_or_ne x b with hxb | hxb
    · subst x
      exact Function.update_self b (some false) f
    · simpa only [g, Function.update_of_ne hxb] using hc x (hold x hxb hx)
  have hind : ∀ x y, g x ≠ none → g y ≠ none → ¬ G.Adj x y := by
    intro x y hx hy
    rcases eq_or_ne x b with hxb | hxb
    · subst x
      rcases eq_or_ne y b with rfl | hyb
      · exact fun h => G.irrefl h
      · exact hnew y (hold y hyb hy)
    · rcases eq_or_ne y b with rfl | hyb
      · exact fun h => hnew x (hold x hxb hx) h.symm
      · exact hi x y (hold x hxb hx) (hold y hyb hy)
  have hr := mono_ready G hmono hind
  have hgf := finite_update hf b false
  exact ⟨g, ⟨update_extends hb false, hgf, ready_stable G hr b false
    (Function.update_self b (some false) f)⟩, _root_.Continuation.TC10R5.ready_wins_three G hgf hr⟩

private theorem star_third_reply {f : V → Option Bool} {a b c : V}
    (hf : HasFiniteDomain f) (ha : f a = some false) (hb : f b = none)
    (hc : f c = some false) (hcover : ∀ x, f x ≠ none → x = a ∨ x = c)
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) (hba : G.Adj b a) (hbc : G.Adj b c) :
    ∃ g, IsLegalResponse G f g b ∧ PartitionerWins G g (3 : Ordinal.{v}) := by
  classical
  let e := triple b a c (G.ne_of_adj hba) (G.ne_of_adj hbc) hac
  let g := Function.update f b (some true)
  have h0 : g b = some true := Function.update_self b (some true) f
  have h1 : g a = some false := by
    simpa only [g, Function.update_of_ne (G.ne_of_adj hba).symm] using ha
  have h2 : g c = some false := by
    simpa only [g, Function.update_of_ne (G.ne_of_adj hbc).symm] using hc
  have hactive : ∀ x, g x ≠ none → ∃ i, e i = x := fun x hx =>
    (eq_or_ne x b).elim (fun h => ⟨0, h.symm⟩)
      (fun h =>
        (hcover x (by simpa only [g, Function.update_of_ne h] using hx)).elim
          (fun hx => ⟨1, hx.symm⟩) (fun hx => ⟨2, hx.symm⟩))
  have hfmono : ∀ x, f x ≠ none → f x = some false := fun x hx =>
    (hcover x hx).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hc)
  have hlegal : UnfriendlyAt G g b :=
    no_same G true h0 fun y hy hy' =>
      let hyOld : f y = some true := by
        simpa only [g, Function.update_of_ne (G.ne_of_adj hy).symm] using hy'
      Bool.noConfusion
        (Option.some.inj ((hfmono y (hyOld ▸ Option.some_ne_none true)).symm.trans hyOld))
  exact ⟨g, ⟨update_extends hb true, finite_update hf b true, hlegal⟩,
    TriangleFreeSix.win_three_of_colored_star G e true hba hbc hnac h0 h1 h2 hactive⟩

/-- Four rounds from a position assigning exactly two distinct nonadjacent
vertices the colour false, on a graph of minimum degree two. -/
theorem nonadjacent_pair_wins_four_false {f : V → Option Bool} {a c : V}
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) (ha : f a = some false) (hc : f c = some false)
    (hcover : ∀ x, f x ≠ none → x = a ∨ x = c)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G f (4 : Ordinal.{v}) := by
  classical
  have hf : HasFiniteDomain f :=
    ((Set.finite_singleton a).union (Set.finite_singleton c)).subset fun x hx => hcover x hx
  have hmono : ∀ x, f x ≠ none → f x = some false :=
    fun x hx => (hcover x hx).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hc)
  have hind : ∀ x y, f x ≠ none → f y ≠ none → ¬ G.Adj x y := by
    intro x y hx hy hxy
    rcases hcover x hx with rfl | rfl <;> rcases hcover y hy with rfl | rfl <;>
      first | exact G.irrefl hxy | exact hnac hxy | exact hnac hxy.symm
  rw [PartitionerWins]
  intro b β hβ
  suffices h : ∃ g, IsLegalResponse G f g b ∧ PartitionerWins G g (3 : Ordinal.{v}) by
    obtain ⟨g, hg, hw⟩ := h
    exact ⟨g, hg, wins_mono G (Order.lt_add_one_iff.mp
      (by simpa only [three_add_one_eq_four] using hβ)) hw⟩
  by_cases hb : f b = none
  · by_cases hba : G.Adj b a
    · by_cases hbc : G.Adj b c
      · exact star_third_reply G hf ha hb hc hcover hac hnac hba hbc
      · exact one_edge_third_reply G ha hb hc hcover hac hnac hba hbc hmin
    · by_cases hbc : G.Adj b c
      · exact one_edge_third_reply G hc hb ha (fun x hx => (hcover x hx).symm)
          hac.symm (fun h => hnac h.symm) hbc hba hmin
      · exact independent_fresh_reply G hf hb hmono hind fun x hx =>
          (hcover x hx).elim (fun h => h.symm ▸ hba) (fun h => h.symm ▸ hbc)
  · have hr := mono_ready G hmono hind
    exact ⟨f, ⟨fun _ _ h => h, hf, ready_stable G hr b false (hmono b hb)⟩,
      _root_.Continuation.TC10R5.ready_wins_three G hf hr⟩

def complementColours (f : V → Option Bool) (x : V) : Option Bool :=
  (f x).map Bool.not

theorem complement_some (f : V → Option Bool) (x : V) (d : Bool) :
    complementColours f x = some d ↔ f x = some (!d) := by
  cases h : f x <;> cases d <;> simp [complementColours, h]

theorem complement_none (f : V → Option Bool) (x : V) :
    complementColours f x = none ↔ f x = none := by
  cases h : f x <;> simp [complementColours, h]

theorem complement_involutive (f : V → Option Bool) :
    complementColours (complementColours f) = f := by
  funext x
  cases h : f x <;> simp [complementColours, h]

private theorem complement_count (f : V → Option Bool) (x : V) (d : Bool) :
    #(NeighColored G (complementColours f) x (some d)) =
      #(NeighColored G f x (some (!d))) :=
  Cardinal.mk_congr (Equiv.subtypeEquivRight fun w =>
    and_congr_right fun _ => complement_some f w d)

theorem complement_legal {f g : V → Option Bool} {x : V}
    (h : IsLegalResponse G f g x) :
    IsLegalResponse G (complementColours f) (complementColours g) x := by
  obtain ⟨b, hb, hbal⟩ := h.2.2
  refine ⟨fun y d hy => (complement_some g y d).mpr
    (h.1 y (!d) ((complement_some f y d).mp hy)),
    h.2.1.subset (fun y hy hn => hy ((complement_none g y).mpr hn)),
    !b, (complement_some g x (!b)).mpr (by simpa only [Bool.not_not] using hb), ?_⟩
  simpa only [complement_count, Bool.not_not] using hbal

theorem wins_complement (α : Ordinal.{v}) (f : V → Option Bool)
    (h : PartitionerWins G f α) : PartitionerWins G (complementColours f) α := by
  induction α using Ordinal.lt_wf.induction generalizing f with
  | h α ih =>
    rw [PartitionerWins] at h ⊢
    intro x β hβ
    obtain ⟨g, hg, hw⟩ := h x β hβ
    exact ⟨complementColours g, complement_legal G hg, ih β hβ g hw⟩

/-- Four rounds from a position assigning exactly two distinct nonadjacent
vertices the same colour, on a graph of minimum degree two. -/
theorem nonadjacent_pair_wins_four {f : V → Option Bool} {a c : V} {d : Bool}
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) (ha : f a = some d) (hc : f c = some d)
    (hcover : ∀ x, f x ≠ none → x = a ∨ x = c)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G f (4 : Ordinal.{v}) := by
  cases d
  · exact nonadjacent_pair_wins_four_false G hac hnac ha hc hcover hmin
  · have hw := nonadjacent_pair_wins_four_false G (f := complementColours f) hac hnac
      ((complement_some f a false).mpr ha) ((complement_some f c false).mpr hc)
      (fun x hx => hcover x (fun hn => hx ((complement_none f x).mpr hn))) hmin
    simpa only [complement_involutive] using wins_complement G 4 (complementColours f) hw

/-- After the standard first and second responses at nonadjacent names, four
rounds remain winnable. -/
theorem second_nonadjacent_wins_four {a c : V} (hac : a ≠ c) (hnac : ¬ G.Adj a c)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G (second G a c) (4 : Ordinal.{v}) := by
  classical
  apply nonadjacent_pair_wins_four_false G hac hnac
  · simp [second, first, Function.update_of_ne hac]
  · simp [second, hnac]
  · intro x hx
    by_contra hn
    have h := not_or.mp hn
    exact hx (by simp [second, first, Function.update_of_ne h.1, Function.update_of_ne h.2,
      emptyPartition])
  · exact hmin

end TenChallenges.Continuation.NamedPositions

end

-- Source: Continuation/UnfriendlyTwoCore.lean
section

/-!
# The two-core preserves every winning clock

The two-core is the union of all induced subgraphs of minimum degree at least
two. Removing its internal edges leaves a forest with at most one core vertex
in each component.
-/

set_option autoImplicit false

universe u v w

namespace TenChallenges.Continuation.TwoCore

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- Every vertex of the set has two distinct neighbours inside it. -/
def HasTwoNeighbors (s : Set V) : Prop :=
  ∀ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, G.Adj x y ∧ G.Adj x z ∧ y ≠ z

/-- The greatest vertex set whose members have two distinct neighbours inside it. -/
def core : Set V := {x | ∃ s, x ∈ s ∧ HasTwoNeighbors G s}

theorem subset_core {s : Set V} (hs : HasTwoNeighbors G s) : s ⊆ core G :=
  fun _ hx => ⟨s, hx, hs⟩

theorem core_hasTwoNeighbors : HasTwoNeighbors G (core G) := by
  exact fun x ⟨s, hx, hs⟩ => let ⟨y, hy, z, hz, ha, hb, hne⟩ := hs x hx
    ⟨y, subset_core G hs hy, z, subset_core G hs hz, ha, hb, hne⟩

theorem core_degree (x : core G) : 2 ≤ #((G.induce (core G)).neighborSet x) := by
  obtain ⟨y, hy, z, hz, ha, hb, hne⟩ := core_hasTwoNeighbors G x x.property
  exact Cardinal.two_le_iff.mpr ⟨⟨⟨y, hy⟩, ha⟩, ⟨⟨z, hz⟩, hb⟩,
    fun e => hne (congrArg (fun a : (G.induce (core G)).neighborSet x => a.val.val) e)⟩

/-- A move on the smaller graph can be lifted through a monotone map on partial colourings. -/
theorem wins_of_projection {W : Type w} (H : SimpleGraph W) (project : V → W)
    (liftColor : (W → Option Bool) → V → Option Bool)
    (hmono : ∀ {c d}, Extends c d → Extends (liftColor c) (liftColor d))
    (hquery : ∀ c x, UnfriendlyAt H c (project x) → UnfriendlyAt G (liftColor c) x)
    (α : Ordinal.{v}) (c : W → Option Bool) (f : V → Option Bool)
    (hf : HasFiniteDomain f) (he : Extends f (liftColor c)) (hw : PartitionerWins H c α) :
    PartitionerWins G f α := by
  induction α using Ordinal.lt_wf.induction generalizing c f with
  | h α ih =>
    rw [PartitionerWins] at hw ⊢
    intro x β hβ
    obtain ⟨d, hd, hw'⟩ := hw (project x) β hβ
    obtain ⟨g, hg, he'⟩ := finite_response_of_unfriendly_partition G (liftColor d) f hf
      (fun y b hy => hmono hd.1 y b (he y b hy)) x (hquery d x hd.2.2)
    exact ⟨g, hg, ih β hβ d g hg.2.1 he' hw'⟩

/-- The graph obtained by deleting the edges internal to the two-core. -/
def forest : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ (x ∈ core G ∧ y ∈ core G)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private theorem forest_le : forest G ≤ G := fun _ _ h => h.1

private theorem two_neighbors_in_subgraph (s : (forest G).Subgraph) (x : V)
    (hc : (s.neighborSet x).ncard = 2) :
    ∃ y ∈ s.verts, ∃ z ∈ s.verts, G.Adj x y ∧ G.Adj x z ∧ y ≠ z := by
  have htwo : 1 < (s.neighborSet x).ncard := hc ▸ Nat.one_lt_two
  obtain ⟨y, hy, z, hz, hne⟩ :=
    (Set.one_lt_ncard (Set.finite_of_ncard_pos (Nat.zero_lt_of_lt htwo))).mp htwo
  exact ⟨y, s.edge_vert (s.adj_symm hy), z, s.edge_vert (s.adj_symm hz),
    forest_le G (s.adj_sub hy), forest_le G (s.adj_sub hz), hne⟩

theorem forest_isAcyclic : (forest G).IsAcyclic := by
  intro x p hp
  have hcore : p.toSubgraph.verts ⊆ core G := subset_core G fun y hy =>
    two_neighbors_in_subgraph G p.toSubgraph y
      (hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hy))
  have he := p.toSubgraph_adj_snd hp.not_nil
  exact (p.adj_snd hp.not_nil).2 ⟨hcore (p.toSubgraph.edge_vert he),
    hcore (p.toSubgraph.edge_vert he.symm)⟩

private theorem absorb (s : Set V)
    (hs : ∀ x ∈ s, x ∉ core G → ∃ y ∈ s, ∃ z ∈ s, G.Adj x y ∧ G.Adj x z ∧ y ≠ z) :
    s ⊆ core G := by
  have hu : HasTwoNeighbors G (core G ∪ s) := by
    intro x hx
    by_cases h : x ∈ core G
    · obtain ⟨y, hy, z, hz, ha⟩ := core_hasTwoNeighbors G x h
      exact ⟨y, Or.inl hy, z, Or.inl hz, ha⟩
    · obtain ⟨y, hy, z, hz, ha⟩ := hs x (hx.resolve_left h) h
      exact ⟨y, Or.inr hy, z, Or.inr hz, ha⟩
  exact fun _ hx => subset_core G hu (Or.inr hx)

theorem eq_of_reachable_core {a b : core G} (hr : (forest G).Reachable a.val b.val) : a = b := by
  classical
  by_contra hne
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have hcore : p.toSubgraph.verts ⊆ core G := by
    apply absorb
    intro x hx hn
    obtain ⟨i, hi, hlen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (p.mem_verts_toSubgraph.mp hx)
    have h0 : i ≠ 0 := fun e => hn (by simpa only [← hi, e, p.getVert_zero] using a.property)
    have hlast : i ≠ p.length := fun e => hn (by
      simpa only [← hi, e, p.getVert_length] using b.property)
    exact hi ▸ two_neighbors_in_subgraph G p.toSubgraph _
      (hp.ncard_neighborSet_toSubgraph_internal_eq_two h0 (lt_of_le_of_ne hlen hlast))
  have hpne := p.not_nil_of_ne (fun e => hne (Subtype.ext e))
  exact (p.adj_snd hpne).2 ⟨a.property, hcore (p.toSubgraph.edge_vert
    (p.toSubgraph_adj_snd hpne).symm)⟩

private noncomputable def componentAnchor (fallback : core G) (C : (forest G).ConnectedComponent) :
    core G := by
  classical
  exact if h : ∃ a : core G, (forest G).connectedComponentMk a.val = C then h.choose else fallback

private noncomputable def project (fallback : core G) (x : V) : core G :=
  componentAnchor G fallback ((forest G).connectedComponentMk x)

private theorem project_core (fallback a : core G) : project G fallback a.val = a := by
  classical
  have hex : ∃ b : core G, (forest G).connectedComponentMk b.val =
      (forest G).connectedComponentMk a.val := ⟨a, rfl⟩
  exact (show componentAnchor G fallback ((forest G).connectedComponentMk a.val) = hex.choose
    from dif_pos hex).trans (eq_of_reachable_core G
      (SimpleGraph.ConnectedComponent.exact hex.choose_spec))

private theorem project_adj (fallback : core G) {x y : V} (h : (forest G).Adj x y) :
    project G fallback x = project G fallback y :=
  congrArg (componentAnchor G fallback) (SimpleGraph.ConnectedComponent.sound h.reachable)

private noncomputable def forestColor (x : V) : Bool :=
  finTwoEquiv ((forest_isAcyclic G).coloringTwo x)

private theorem forestColor_ne {x y : V} (h : (forest G).Adj x y) :
    forestColor G x ≠ forestColor G y :=
  fun e => (forest_isAcyclic G).coloringTwo.valid h (finTwoEquiv.injective e)

private noncomputable def liftColor (fallback : core G) (c : core G → Option Bool) (x : V) :
    Option Bool :=
  (c (project G fallback x)).map fun b =>
    if forestColor G x = forestColor G (project G fallback x).val then b else !b

private theorem liftColor_core (fallback : core G) (c : core G → Option Bool) (a : core G) :
    liftColor G fallback c a.val = c a := by
  simp [liftColor, project_core]

private theorem liftColor_extends (fallback : core G) {c d : core G → Option Bool}
    (h : Extends c d) : Extends (liftColor G fallback c) (liftColor G fallback d) := by
  intro x b hx
  obtain ⟨e, he, _⟩ := Option.map_eq_some_iff.mp hx
  simpa only [liftColor, h _ e he, he] using hx


private theorem liftColor_edge (fallback : core G) (c : core G → Option Bool) {x y : V}
    (he : (forest G).Adj x y) (b : Bool) (hx : liftColor G fallback c x = some b) :
    liftColor G fallback c y ≠ some b := by
  have hn := forestColor_ne G he
  simp only [liftColor, project_adj G fallback he] at hx ⊢
  exact (show ∀ (d e r b : Bool) (o : Option Bool), d ≠ e →
      o.map (fun z => if d = r then z else !z) = some b →
      o.map (fun z => if e = r then z else !z) ≠ some b by decide) _ _ _ _ _ hn hx

private theorem liftColor_unfriendly (fallback : core G) (c : core G → Option Bool) (x : V)
    (hq : UnfriendlyAt (G.induce (core G)) c (project G fallback x)) :
    UnfriendlyAt G (liftColor G fallback c) x := by
  classical
  by_cases hx : x ∈ core G
  · let a : core G := ⟨x, hx⟩
    have hqa : UnfriendlyAt (G.induce (core G)) c a := project_core G fallback a ▸ hq
    obtain ⟨b, hb, hc⟩ := hqa
    have hbx : liftColor G fallback c x = some b := (liftColor_core G fallback c a).trans hb
    refine ⟨b, hbx, ?_⟩
    have mem (y : NeighColored G (liftColor G fallback c) x (some b)) : y.val ∈ core G :=
      Classical.byContradiction fun hy => liftColor_edge G fallback c
        ⟨y.property.1, fun e => hy e.2⟩ b hbx y.property.2
    let toCore : NeighColored G (liftColor G fallback c) x (some b) ↪
        NeighColored (G.induce (core G)) c a (some b) := {
      toFun := fun y => ⟨⟨y.val, mem y⟩, y.property.1,
        (liftColor_core G fallback c ⟨y.val, mem y⟩).symm.trans y.property.2⟩
      inj' := fun _ _ e => Subtype.ext (congrArg (fun z => z.val.val) e) }
    let fromCore : NeighColored (G.induce (core G)) c a (some (!b)) ↪
        NeighColored G (liftColor G fallback c) x (some (!b)) := {
      toFun := fun y => ⟨y.val.val, y.property.1, (liftColor_core G fallback c y.val).trans
        y.property.2⟩
      inj' := fun _ _ e => Subtype.ext (Subtype.ext (congrArg
        (fun z : NeighColored G (liftColor G fallback c) x (some (!b)) => z.val) e)) }
    exact ((Cardinal.le_def ..).mpr ⟨toCore⟩).trans (hc.trans ((Cardinal.le_def ..).mpr ⟨fromCore⟩))
  · obtain ⟨b, hb, _⟩ := hq
    let d := if forestColor G x = forestColor G (project G fallback x).val then b else !b
    have hd : liftColor G fallback c x = some d := by simp [liftColor, hb, d]
    exact _root_.Continuation.TC10.no_same G d hd fun _ ha =>
      liftColor_edge G fallback c ⟨ha, fun e => hx e.1⟩ d hd

/-- A win from the empty two-core lifts to the same ordinal clock on the full graph. -/
theorem partitionerWins_of_twoCore (α : Ordinal.{v})
    (hw : PartitionerWins (G.induce (core G)) (emptyPartition (core G)) α) :
    PartitionerWins G (emptyPartition V) α := by
  classical
  by_cases h : (core G).Nonempty
  · let fallback : core G := ⟨h.choose, h.choose_spec⟩
    exact wins_of_projection G (G.induce (core G)) (project G fallback) (liftColor G fallback)
      (liftColor_extends G fallback) (liftColor_unfriendly G fallback) α _ _
      (by simp [HasFiniteDomain, emptyPartition]) (by simp [Extends, emptyPartition]) hw
  · apply partitionerWins_of_unfriendly_partition G (fun x => some (forestColor G x)) _ α
    intro x
    exact _root_.Continuation.TC10.no_same G _ rfl fun y ha e =>
      forestColor_ne G (show (forest G).Adj x y from ⟨ha, fun hh => h ⟨x, hh.1⟩⟩)
        (Option.some.inj e).symm

end TenChallenges.Continuation.TwoCore

end

-- Source: Continuation/UnfriendlySealedBlock.lean
section

set_option autoImplicit false

universe u v
namespace TenChallenges.Continuation.SealedBlock

open Classical
open scoped Cardinal
open _root_.Continuation.TC10 (first second second_legal_ready wins_mono unique_same)

variable {V : Type u} (G : SimpleGraph V)

private noncomputable def liftColour (B : Set V) (anchor : (Bᶜ : Set V))
    (flip : V → Bool) (c : (Bᶜ : Set V) → Option Bool) (x : V) : Option Bool :=
  if h : x ∈ B then (c anchor).map (fun b => if flip x then !b else b) else c ⟨x, h⟩

private noncomputable def project (B : Set V) (anchor : (Bᶜ : Set V)) (x : V) :
    (Bᶜ : Set V) := if h : x ∈ B then anchor else ⟨x, h⟩

private lemma lift_inside {B : Set V} {anchor : (Bᶜ : Set V)} {flip : V → Bool}
    {c : (Bᶜ : Set V) → Option Bool} {x : V} (hx : x ∈ B) :
    liftColour B anchor flip c x = (c anchor).map (fun b => if flip x then !b else b) :=
  dif_pos hx

private lemma lift_outside {B : Set V} {anchor : (Bᶜ : Set V)} {flip : V → Bool}
    {c : (Bᶜ : Set V) → Option Bool} (x : (Bᶜ : Set V)) :
    liftColour B anchor flip c x.val = c x :=
  dif_neg x.property

private lemma lift_mono {B : Set V} {anchor : (Bᶜ : Set V)} {flip : V → Bool}
    {c d : (Bᶜ : Set V) → Option Bool} (h : Extends c d) :
    Extends (liftColour B anchor flip c) (liftColour B anchor flip d) := by
  intro x b hb
  by_cases hx : x ∈ B
  · exact let ⟨a, ha, hab⟩ := Option.map_eq_some_iff.mp ((lift_inside hx).symm.trans hb)
    (lift_inside hx).trans (Option.map_eq_some_iff.mpr ⟨a, h anchor a ha, hab⟩)
  · exact (lift_outside ⟨x, hx⟩).trans
      (h ⟨x, hx⟩ b ((lift_outside ⟨x, hx⟩).symm.trans hb))

private theorem unfriendly_of_induce {S : Set V} {f : V → Option Bool} {d : S → Option Bool}
    (x : S) (hin : ∀ y : S, f y.val = d y)
    (hout : ∀ y ∉ S, G.Adj x.val y → ∀ b, f x.val = some b → f y ≠ some b)
    (h : UnfriendlyAt (G.induce S) d x) : UnfriendlyAt G f x.val := by
  obtain ⟨b, hb, hcard⟩ := h
  have hx : f x.val = some b := (hin x).trans hb
  refine ⟨b, hx, ?_⟩
  let e : NeighColored G f x.val (some b) ↪ NeighColored (G.induce S) d x (some b) := by
    refine ⟨?_, ?_⟩
    · intro y
      have hy : y.val ∈ S := Classical.byContradiction
        (fun hn => hout y.val hn y.property.1 b hx y.property.2)
      exact ⟨⟨y.val, hy⟩, y.property.1, (hin ⟨y.val, hy⟩).symm.trans y.property.2⟩
    · intro y z hyz
      exact Subtype.ext (congrArg (fun w : NeighColored (G.induce S) d x (some b) => w.val.val) hyz)
  let e' : NeighColored (G.induce S) d x (some (!b)) ↪ NeighColored G f x.val (some (!b)) :=
    ⟨fun y => ⟨y.val.val, y.property.1, (hin y.val).trans y.property.2⟩,
      fun _ _ hEq => Subtype.ext (Subtype.ext (congrArg (fun w : NeighColored G f x.val (some (!b)) => w.val) hEq))⟩
  exact ((Cardinal.le_def ..).mpr ⟨e⟩).trans (hcard.trans ((Cardinal.le_def ..).mpr ⟨e'⟩))

private theorem lift_query {B : Set V} {anchor : (Bᶜ : Set V)} {flip : V → Bool}
    (hcross : ∀ (x : (Bᶜ : Set V)) y, y ∈ B → G.Adj x.val y → x = anchor ∧ flip y = true)
    (hblock : ∀ c b, c anchor = some b → ∀ x ∈ B, UnfriendlyAt G (liftColour B anchor flip c) x)
    (c : (Bᶜ : Set V) → Option Bool) (x : V)
    (hx : UnfriendlyAt (G.induce (Bᶜ : Set V)) c (project B anchor x)) :
    UnfriendlyAt G (liftColour B anchor flip c) x := by
  by_cases h : x ∈ B
  · exact let ⟨b, hb, _⟩ := (show UnfriendlyAt (G.induce (Bᶜ : Set V)) c anchor from
      by simpa only [project, dif_pos h] using hx)
    hblock c b hb x h
  · refine unfriendly_of_induce G (S := Bᶜ) ⟨x, h⟩ lift_outside ?_
      (by simpa only [project, dif_neg h] using hx)
    exact fun y hy hxy b hb =>
      let hyB : y ∈ B := Classical.not_not.mp (show ¬¬ y ∈ B from hy)
      let ⟨ha, hflip⟩ := hcross ⟨x, h⟩ y hyB hxy
      have ht : c anchor = some b := ha ▸ (lift_outside ⟨x, h⟩).symm.trans hb
      by simp [lift_inside hyB, ht, hflip]

private theorem lift_wins {B : Set V} (anchor : (Bᶜ : Set V)) (flip : V → Bool)
    (hcross : ∀ (x : (Bᶜ : Set V)) y, y ∈ B → G.Adj x.val y → x = anchor ∧ flip y = true)
    (hblock : ∀ c b, c anchor = some b → ∀ x ∈ B, UnfriendlyAt G (liftColour B anchor flip c) x)
    {α : Ordinal.{v}} {c : (Bᶜ : Set V) → Option Bool} (hw : PartitionerWins (G.induce (Bᶜ : Set V)) c α)
    {f : V → Option Bool} (hf : HasFiniteDomain f) (he : Extends f (liftColour B anchor flip c)) :
    PartitionerWins G f α :=
  TwoCore.wins_of_projection G _ (project B anchor) (liftColour B anchor flip)
    lift_mono (lift_query G hcross hblock) α c f hf he hw

theorem first_wins_four (a : V) : PartitionerWins G (first a) (4 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun b β hβ => let h := second_legal_ready G a b
    ⟨second G a b, h.1, wins_mono G
      (Order.lt_succ_iff.mp (((Nat.cast_add_one (R := Ordinal.{v}) 3).trans
        (Order.succ_eq_add_one (3 : Ordinal.{v})).symm) ▸ hβ))
      (_root_.Continuation.TC10R5.ready_wins_three G h.1.2.1 h.2)⟩

/-- Four vertices whose displayed neighbourhoods leave only one exterior anchor. -/
structure Trap where
  vertices : Fin 5 ↪ V
  row_zero : G.neighborSet (vertices 0) = {vertices 1, vertices 2, vertices 3}
  row_one : G.neighborSet (vertices 1) = {vertices 0, vertices 2, vertices 3}
  row_two : G.neighborSet (vertices 2) = {vertices 0, vertices 1, vertices 4}
  row_three : G.neighborSet (vertices 3) = {vertices 0, vertices 1, vertices 4}

namespace Trap

variable {G} (T : Trap G)

private def block : Set V := {T.vertices 0, T.vertices 1, T.vertices 2, T.vertices 3}

private noncomputable def flip (x : V) : Bool :=
  if x = T.vertices 2 ∨ x = T.vertices 3 then true else false

private lemma anchor_outside : T.vertices 4 ∉ T.block := by simp [block]

private def anchor : (T.blockᶜ : Set V) := ⟨T.vertices 4, T.anchor_outside⟩

private noncomputable def colour := liftColour T.block T.anchor T.flip (first T.anchor)

private theorem cross (x : (T.blockᶜ : Set V)) (y : V) (hy : y ∈ T.block)
    (hxy : G.Adj x.val y) : x = T.anchor ∧ T.flip y = true := by
  have hn : x.val ∉ T.block := x.property
  rcases (show y = T.vertices 0 ∨ y = T.vertices 1 ∨ y = T.vertices 2 ∨ y = T.vertices 3 by
    simpa [block] using hy) with rfl | rfl | rfl | rfl
  all_goals have hm : x.val ∈ G.neighborSet _ := hxy.symm
  all_goals simp_all [block, flip, anchor, T.row_zero, T.row_one, T.row_two, T.row_three]
  all_goals exact Subtype.ext hm

private theorem stable_row {f : V → Option Bool} {x same opp₁ opp₂ : V} {b : Bool}
    (row : G.neighborSet x = {same, opp₁, opp₂}) (hx : f x = some b)
    (h₁ : f opp₁ = some (!b)) (h₂ : f opp₂ = some (!b)) : UnfriendlyAt G f x := by
  refine unique_same G b hx ((Set.subsingleton_singleton (a := same)).anti ?_)
    ⟨opp₁, ?_, h₁⟩
  · intro y hy
    rcases (show y ∈ ({same, opp₁, opp₂} : Set V) from row ▸ hy.1) with rfl | rfl | rfl
    · simp
    · exact (Bool.not_ne_self b (Option.some.inj (h₁.symm.trans hy.2))).elim
    · exact (Bool.not_ne_self b (Option.some.inj (h₂.symm.trans hy.2))).elim
  · exact show opp₁ ∈ G.neighborSet x from row.symm ▸ (by simp)

private theorem block_unfriendly (c : (T.blockᶜ : Set V) → Option Bool) (b : Bool)
    (hb : c T.anchor = some b) (x : V) (hx : x ∈ T.block) :
    UnfriendlyAt G (liftColour T.block T.anchor T.flip c) x := by
  have hc (i : Fin 5) (hi : T.vertices i ∈ T.block) :
      liftColour T.block T.anchor T.flip c (T.vertices i) =
        some (if i = 2 ∨ i = 3 then !b else b) := by
    simp [lift_inside hi, hb, flip]
  have hreorder : ({T.vertices 0, T.vertices 1, T.vertices 4} : Set V) =
      {T.vertices 4, T.vertices 0, T.vertices 1} := by
    rw [Set.pair_comm (T.vertices 1) (T.vertices 4), Set.insert_comm (T.vertices 0) (T.vertices 4)]
  rcases (show x = T.vertices 0 ∨ x = T.vertices 1 ∨ x = T.vertices 2 ∨ x = T.vertices 3 by
    simpa [block] using hx) with rfl | rfl | rfl | rfl
  · exact stable_row (b := b) T.row_zero (by simpa using hc 0 hx)
      (by simpa using hc 2 (by simp [block])) (by simpa using hc 3 (by simp [block]))
  · exact stable_row (b := b) T.row_one (by simpa using hc 1 hx)
      (by simpa using hc 2 (by simp [block])) (by simpa using hc 3 (by simp [block]))
  · exact stable_row (b := !b) (T.row_two.trans hreorder) (by simpa using hc 2 hx)
      (by simpa using hc 0 (by simp [block])) (by simpa using hc 1 (by simp [block]))
  · exact stable_row (b := !b) (T.row_three.trans hreorder) (by simpa using hc 3 hx)
      (by simpa using hc 0 (by simp [block])) (by simpa using hc 1 (by simp [block]))

private theorem colour_finite : HasFiniteDomain T.colour := by
  refine ((show T.block.Finite by simp [block]).union (Set.finite_singleton (T.vertices 4))).subset ?_
  intro x hx
  by_cases h : x ∈ T.block
  · exact Or.inl h
  · refine Or.inr (Classical.byContradiction (fun hn => hx ?_))
    have hne : (⟨x, h⟩ : (T.blockᶜ : Set V)) ≠ T.anchor :=
      fun e => hn (congrArg Subtype.val e)
    exact (lift_outside (⟨x, h⟩ : (T.blockᶜ : Set V))).trans
      (@Function.update_of_ne _ (fun _ => Option Bool) (Classical.decEq _)
        _ _ hne (some false) (emptyPartition _))

private theorem first_extends : Extends (first (T.vertices 0)) T.colour := by
  intro x b hx
  simp [first, Function.update_apply, emptyPartition, ite_eq_iff] at hx
  rcases hx with ⟨rfl, rfl⟩
  simp [colour, lift_inside (show T.vertices 0 ∈ T.block by simp [block]), first, flip]

/-- Replying with the two vertices of indices zero and one and the anchor all coloured
false, and the other two vertices true, leaves four moves to play. -/
theorem response : ∃ q, IsLegalResponse G (first (T.vertices 0)) q (T.vertices 1) ∧
    PartitionerWins G q (4 : Ordinal.{v}) := by
  exact ⟨T.colour, ⟨T.first_extends, T.colour_finite,
    T.block_unfriendly _ false (by simp [first]) _ (by simp [block])⟩,
    lift_wins G T.anchor T.flip T.cross T.block_unfriendly
      (first_wins_four _ T.anchor) T.colour_finite (fun _ _ h => h)⟩

end Trap
end TenChallenges.Continuation.SealedBlock

end

-- Source: Continuation/UnfriendlyAdjacentPositions.lean
section

/-! # Third queries after a properly coloured first edge -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.AdjacentPositions

open NamedPositions
open _root_.Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

abbrev Reply (f : V → Option Bool) (c : V) : Prop :=
  ∃ g, IsLegalResponse G f g c ∧ PartitionerWins G g (3 : Ordinal.{v})

structure PairState (f : V → Option Bool) (a b : V) : Prop where
  left : f a = some false
  right : f b = some true
  support : ∀ x, f x ≠ none → x = a ∨ x = b

theorem PairState.flip {f : V → Option Bool} {a b : V} (h : PairState f a b) :
    PairState (complementColours f) b a :=
  ⟨(complement_some f b false).mpr h.right, (complement_some f a true).mpr h.left,
    fun x hx => (h.support x (fun hn => hx ((complement_none f x).mpr hn))).symm⟩

theorem PairState.extends {f g : V → Option Bool} {a b : V} (h : PairState f a b)
    (ha : g a = some false) (hb : g b = some true) : Extends f g := by
  intro x d hx
  rcases h.support x (hx ▸ Option.some_ne_none d) with rfl | rfl
  · exact ha.trans (h.left.symm.trans hx)
  · exact hb.trans (h.right.symm.trans hx)

theorem reply_from_extension {f g : V → Option Bool} {c : V}
    (he : Extends f g) (hr : Reply.{u,v} G g c) : Reply.{u,v} G f c :=
  let ⟨p, hp, hw⟩ := hr
  ⟨p, ⟨fun x d hx => hp.1 x d (he x d hx), hp.2⟩, hw⟩

theorem reply_of_complement {f : V → Option Bool} {c : V}
    (h : Reply.{u,v} G (complementColours f) c) : Reply.{u,v} G f c := by
  obtain ⟨p, hp, hw⟩ := h
  exact ⟨complementColours p, by simpa only [complement_involutive] using complement_legal G hp,
    wins_complement G 3 p hw⟩

theorem named_reply {n : ℕ} {e : Fin n ↪ V} {A : Edges n} (he : Realizes G e A)
    {f : V → Option Bool} (p : Colours n) (i : Fin n) (hf : Extends f (position e p))
    (hbal : Balanced A p i) (hw : PartitionerWins G (position e p) (3 : Ordinal.{v})) :
    Reply.{u,v} G f (e i) :=
  let ⟨b,hb,hle⟩ := hbal
  ⟨position e p, ⟨hf, position_finite _ _, b, (position_name _ _ _).trans hb,
    by simpa only [count_eq G he, Nat.cast_le] using hle⟩, hw⟩

def HasTrap (a b : V) : Prop :=
  ∃ T : SealedBlock.Trap G, T.vertices 0 = a ∧ T.vertices 1 = b

theorem trap_of_rows {a b x y t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ t) (hy : y ≠ a ∧ y ≠ b ∧ y ≠ t) (hxy : x ≠ y)
    (ha : G.neighborSet a = {b,x,y}) (hb : G.neighborSet b = {a,x,y})
    (hrx : G.neighborSet x = {a,b,t}) (hry : G.neighborSet y = {a,b,t}) : HasTrap G a b := by
  let verts : Fin 5 ↪ V := ⟨![a,b,x,y,t], by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]⟩
  exact ⟨⟨verts,ha,hb,hrx,hry⟩,rfl,rfl⟩

theorem encard_of_cubic {v : V} (h : #(G.neighborSet v) = 3) :
    (G.neighborSet v).encard = 3 := by simp [← Set.toENat_cardinalMk, h]

theorem row_from_three {s : Set V} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hs : s.encard ≤ 3) :
    s = {a,b,c} :=
  ((show ({a,b,c} : Set V).Finite by simp).eq_of_subset_of_encard_le
    (by simpa only [Set.insert_subset_iff, Set.singleton_subset_iff] using And.intro ha ⟨hb,hc⟩)
    (hs.trans_eq (Set.encard_eq_three.mpr ⟨a,b,c,hab,hac,hbc,rfl⟩).symm)).symm

theorem cubic_external {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : b ≠ c) (hdeg : #(G.neighborSet a) = 3) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ G.neighborSet a = {b,c,x} := by
  have hcard := encard_of_cubic G hdeg
  have hout : ¬ G.neighborSet a ⊆ ({b,c} : Set V) := fun hsub =>
    (by decide : ¬ (3 : ℕ∞) ≤ 2) (hcard ▸ Set.encard_pair hbc ▸ Set.encard_mono hsub)
  obtain ⟨x, hx, hxc⟩ := Set.not_subset.mp hout
  have hd : x ≠ b ∧ x ≠ c := by simpa using hxc
  exact ⟨x, (G.ne_of_adj hx).symm, hd.1, hd.2,
    row_from_three hbc hd.1.symm hd.2.symm hab hac hx hcard.le⟩

theorem realizes_edge {a b c : V} (hab : G.Adj a b) (hac : ¬G.Adj a c) (hbc : ¬G.Adj b c)
    {hab' : a ≠ b} {hac' : a ≠ c} {hbc' : b ≠ c} :
    Realizes G (triple a b c hab' hac' hbc') edge3 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact ⟨fun h => Bool.noConfusion h, fun h => (G.irrefl h).elim⟩
    | exact ⟨fun _ => hab, fun _ => rfl⟩
    | exact ⟨fun _ => hab.symm, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => (hac h).elim⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => (hac h.symm).elim⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => (hbc h).elim⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => (hbc h.symm).elim⟩

theorem realizes_triangle {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    {hab' : a ≠ b} {hac' : a ≠ c} {hbc' : b ≠ c} :
    Realizes G (triple a b c hab' hac' hbc') TriangleReplies.tri3 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact ⟨fun h => Bool.noConfusion h, fun h => (G.irrefl h).elim⟩
    | exact ⟨fun _ => hab, fun _ => rfl⟩
    | exact ⟨fun _ => hab.symm, fun _ => rfl⟩
    | exact ⟨fun _ => hac, fun _ => rfl⟩
    | exact ⟨fun _ => hac.symm, fun _ => rfl⟩
    | exact ⟨fun _ => hbc, fun _ => rfl⟩
    | exact ⟨fun _ => hbc.symm, fun _ => rfl⟩

end TenChallenges.Continuation.AdjacentPositions

end

-- Source: Continuation/UnfriendlyAdjacentReplies.lean
section

/-! # Isolated queries and noncubic triangles after the first edge -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.AdjacentPositions

open NamedPositions
open _root_.Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

private theorem not_named {a b c x : V} {hab : a ≠ b} {hac : a ≠ c} {hbc : b ≠ c}
    (hx : x ∉ Set.range (triple a b c hab hac hbc)) : x ≠ a ∧ x ≠ b ∧ x ≠ c :=
  ⟨fun h => hx ⟨0,h.symm⟩, fun h => hx ⟨1,h.symm⟩, fun h => hx ⟨2,h.symm⟩⟩

private def TwinRows (a b c : V) : Prop :=
  ∃ x y, (x ≠ a ∧ x ≠ b ∧ x ≠ c) ∧ (y ≠ a ∧ y ≠ b ∧ y ≠ c) ∧ x ≠ y ∧
    G.neighborSet b = {a,x,y} ∧ G.neighborSet x = {a,b,c} ∧ G.neighborSet y = {a,b,c}

private theorem isolate_one_side {a b c : V} {f : V → Option Bool} (h : PairState f a b)
    (hab : G.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) (hna : ¬G.Adj a c) (hnb : ¬G.Adj b c)
    (hmin : ∀ v, (2 : Cardinal) ≤ #(G.neighborSet v)) : Reply.{u,v} G f c ∨ TwinRows G a b c := by
  let e := triple a b c hab.ne hac hbc
  have he : Realizes G e edge3 := realizes_edge G hab hna hnb
  rcases edge_isolate_wins_three_or_neighborhoods G he hmin with hw | ⟨x,y,hx,hy,hxy,hb,hr,hs⟩
  · exact Or.inl (named_reply G he edgeColours3 2 (h.extends (position_name e _ 0)
      (position_name e _ 1)) (by decide) hw)
  · exact Or.inr ⟨x,y,not_named hx,not_named hy,hxy,hb,hr,hs⟩

theorem isolated_reply {a b c : V} {f : V → Option Bool} (h : PairState f a b)
    (hab : G.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) (hna : ¬G.Adj a c) (hnb : ¬G.Adj b c)
    (hmin : ∀ v, (2 : Cardinal) ≤ #(G.neighborSet v)) (ht : ¬ HasTrap G a b) : Reply.{u,v} G f c := by
  rcases isolate_one_side G h hab hac hbc hna hnb hmin with hw | ⟨x,y,hx,hy,hxy,hb,hrx,hry⟩
  · exact hw
  rcases isolate_one_side G h.flip hab.symm hbc hac hnb hna hmin with hw | ⟨r,s,hr,hs,hrs,ha,_,_⟩
  · exact reply_of_complement G hw
  have hxa : G.Adj x a := show a ∈ G.neighborSet x from hrx.symm ▸ (by simp)
  have hya : G.Adj y a := show a ∈ G.neighborSet y from hry.symm ▸ (by simp)
  have hsize : (G.neighborSet a).encard = 3 :=
    Set.encard_eq_three.mpr ⟨b,r,s,hr.1.symm,hs.1.symm,hrs,ha⟩
  have hrow := row_from_three (s := G.neighborSet a) hx.2.1.symm hy.2.1.symm hxy
    hab hxa.symm hya.symm hsize.le
  exact (ht (trap_of_rows G hab.ne hac hbc hx hy hxy hrow hb hrx hry)).elim

theorem star_reply {a b c : V} {f : V → Option Bool} (h : PairState f a b)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c) (hnb : ¬G.Adj b c) : Reply.{u,v} G f c := by
  let e := triple a b c hab.ne hac.ne hbc
  let p : Colours 3 := ![some false, some true, some true]
  let g := position e p
  have h0 : g a = some false := position_name e p 0
  have h1 : g b = some true := position_name e p 1
  have h2 : g c = some true := position_name e p 2
  have hs (x : V) (hx : g x ≠ none) : x ∈ Set.range e :=
    Classical.byContradiction fun hn => hx (position_outside p hn)
  have hlegal : UnfriendlyAt G g c := by
    refine no_same G true h2 ?_
    intro z hcz hz
    obtain ⟨i,rfl⟩ := hs z (hz ▸ Option.some_ne_none true)
    fin_cases i
    · exact Bool.noConfusion (Option.some.inj (h0.symm.trans hz))
    · exact hnb hcz.symm
    · exact G.irrefl hcz
  exact ⟨g, ⟨h.extends h0 h1,position_finite e p,hlegal⟩,
    TriangleFreeSix.win_three_of_colored_star G e false hab hac hnb h0 h1 h2 hs⟩

theorem triangle_one_side {a b c : V} {f : V → Option Bool} (h : PairState f a b)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hmin : ∀ v, (2 : Cardinal) ≤ #(G.neighborSet v)) :
    Reply.{u,v} G f c ∨ (#(G.neighborSet a) = 3 ∧ #(G.neighborSet c) = 3) := by
  let e := triple a c b hac.ne hab.ne hbc.ne.symm
  have he : Realizes G e TriangleReplies.tri3 := realizes_triangle G hac hab hbc.symm
  rcases TriangleReplies.colored_triangle_wins_three_or_both_cubic G he hmin with hw | hdeg
  · exact Or.inl (named_reply G he TriangleReplies.triStart 1 (h.extends (position_name e _ 0)
      (position_name e _ 2)) (by decide) hw)
  · exact Or.inr hdeg

end TenChallenges.Continuation.AdjacentPositions

end

-- Source: Continuation/UnfriendlyCubicExposed.lean
section

/-! # Exposed-colour replies at cubic triangles -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.NamedPositions.TriangleReplies

open _root_.Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The queried name one is unassigned. Names zero and two have opposite colours. -/
def beforeExposedTriangle : Colours 3 := ![some false, none, some true]

private def sharedDiagram (b : Bool) : Edges 4 :=
  appendRow tri3 ![true, true, b]

private def firstDistinctDiagram : Edges 4 :=
  appendRow tri3 ![true, false, false]

private def distinctDiagram (b : Bool) : Edges 5 :=
  appendRow firstDistinctDiagram ![false, true, false, b]

private def exposed4 : Colours 4 := triColours4 true
private def exposed5 : Colours 5 := triColours5 (some true) (some true)

private theorem checked_shared : ∀ (b : Bool) (i : Fin 4), Balanced (sharedDiagram b) exposed4 i := by
  decide +kernel

private theorem checked_distinct : ∀ (b : Bool) (i : Fin 5), Balanced (distinctDiagram b) exposed5 i := by
  decide +kernel

private theorem extends_exposed4 : Extends (Fin.snoc beforeExposedTriangle none) exposed4 := by
  unfold Extends
  decide +kernel

private theorem extends_exposed5 :
    Extends (Fin.snoc (Fin.snoc beforeExposedTriangle none) none) exposed5 := by
  unfold Extends
  decide +kernel

private theorem exposed4_total : ∀ i : Fin 4, exposed4 i ≠ none := by decide
private theorem exposed5_total : ∀ i : Fin 5, exposed5 i ≠ none := by decide
private theorem exposed4_false : ∀ i : Fin 4, exposed4 i = some false → i = 0 ∨ i = 1 := by decide
private theorem exposed5_false : ∀ i : Fin 5, exposed5 i = some false → i = 0 ∨ i = 1 := by decide

private theorem external_adj {e : Fin 3 ↪ V} {i j k : Fin 3} {r x : V}
    (h : G.neighborSet (e i) = {e j, e k, r}) (hx : x ∉ Set.range e) :
    G.Adj x (e i) ↔ x = r := by
  have hj : x ≠ e j := fun e' => hx ⟨j, e'.symm⟩
  have hk : x ≠ e k := fun e' => hx ⟨k, e'.symm⟩
  rw [G.adj_comm x (e i), ← SimpleGraph.mem_neighborSet, h]
  simp [hj, hk]

private theorem exact_row_sealed {n : ℕ} {e : Fin n ↪ V} {i j k l : Fin n}
    (h : G.neighborSet (e i) = {e j, e k, e l}) :
    G.neighborSet (e i) ⊆ Set.range e := by
  rw [h]
  exact Set.insert_subset_iff.mpr
    ⟨⟨j, rfl⟩, Set.insert_subset_iff.mpr ⟨⟨k, rfl⟩, Set.singleton_subset_iff.mpr ⟨l, rfl⟩⟩⟩

private theorem exposed_reply {n : ℕ} {e : Fin n ↪ V} {A : Edges n} {f p : Colours n}
    (i : Fin n) (he : Realizes G e A) (hExt : Extends f p)
    (hbal : ∀ j, Balanced A p j) (hfull : ∀ j, p j ≠ none)
    (hSeal : ∀ j, p j = some false → G.neighborSet (e j) ⊆ Set.range e) :
    ∃ g, IsLegalResponse G (position e f) g (e i) ∧ PartitionerWins G g (3 : Ordinal.{v}) := by
  let g := position e p
  have hnamed {x : V} {b : Bool} (h : g x = some b) : x ∈ Set.range e :=
    Classical.byContradiction fun hx => Option.some_ne_none b (h.symm.trans (position_outside p hx))
  have hExt' : Extends (position e f) g := by
    intro x b hx
    by_cases hn : x ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hn
      exact (position_name e p j).trans (hExt j b ((position_name e f j).symm.trans hx))
    · exact (Option.some_ne_none b (hx.symm.trans (position_outside f hn))).elim
  have hStable : Stable G g := by
    intro x b hx
    obtain ⟨j, rfl⟩ := hnamed hx
    obtain ⟨d, hd, hcount⟩ := hbal j
    exact ⟨d, (position_name e p j).trans hd,
      by simpa only [g, count_eq G he, Nat.cast_le] using hcount⟩
  have hSealed : _root_.Continuation.TC10R6.SealedColour G g true := by
    intro x hx y hy hxy
    obtain ⟨j, rfl⟩ := hnamed hy
    obtain ⟨k, rfl⟩ := hSeal j ((position_name e p j).symm.trans hy) hxy.symm
    exact hfull k ((position_name e p k).symm.trans hx)
  obtain ⟨d, hd, _⟩ := hbal i
  exact ⟨g, ⟨hExt', position_finite e p, hStable (e i) d ((position_name e p i).trans hd)⟩,
    _root_.Continuation.TC10R6.exposed_wins_three G (position_finite e p) hStable hSealed⟩

/-- If the matching pair shares its external neighbour, assigning that
neighbour the minority colour gives a legal three-round reply. -/
theorem cubic_triangle_shared_exposed_reply {e : Fin 3 ↪ V} (he : Realizes G e tri3)
    {r : V} (hr : r ∉ Set.range e)
    (h0 : G.neighborSet (e 0) = {e 1, e 2, r})
    (h1 : G.neighborSet (e 1) = {e 0, e 2, r}) :
    ∃ g, IsLegalResponse G (position e beforeExposedTriangle) g (e 1) ∧
      PartitionerWins G g (3 : Ordinal.{v}) := by
  classical
  let e4 := appendName e r hr
  let b := decide (G.Adj r (e 2))
  have hrow (i : Fin 3) : (![true, true, b] : Fin 3 → Bool) i = true ↔ G.Adj r (e i) := by
    fin_cases i
    · exact ⟨fun _ => (external_adj G h0 hr).mpr rfl, fun _ => rfl⟩
    · exact ⟨fun _ => (external_adj G h1 hr).mpr rfl, fun _ => rfl⟩
    · exact decide_eq_true_iff
  have he4 : Realizes G e4 (sharedDiagram b) :=
    realizes_appendRow G he r hr _ hrow
  have hSeal (i : Fin 4) (hi : exposed4 i = some false) :
      G.neighborSet (e4 i) ⊆ Set.range e4 := by
    rcases exposed4_false i hi with rfl | rfl
    · exact exact_row_sealed G (i := 0) (j := 1) (k := 2) (l := 3) h0
    · exact exact_row_sealed G (i := 1) (j := 0) (k := 2) (l := 3) h1
  have hreply := exposed_reply G 1 he4 extends_exposed4 (checked_shared b) exposed4_total hSeal
  simpa only [e4, position_append_none,
    show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, appendName_castSucc] using hreply

/-- For distinct external neighbours, give the minority colour to the two
external neighbours of the matching pair. -/
theorem cubic_triangle_distinct_exposed_reply {e : Fin 3 ↪ V} (he : Realizes G e tri3)
    {x y z : V} (hx : x ∉ Set.range e) (hy : y ∉ Set.range e)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : G.neighborSet (e 0) = {e 1, e 2, x})
    (h1 : G.neighborSet (e 1) = {e 0, e 2, y})
    (h2 : G.neighborSet (e 2) = {e 0, e 1, z}) :
    ∃ g, IsLegalResponse G (position e beforeExposedTriangle) g (e 1) ∧
      PartitionerWins G g (3 : Ordinal.{v}) := by
  classical
  let e4 := appendName e x hx
  have hxrow (i : Fin 3) : (![true, false, false] : Fin 3 → Bool) i = true ↔ G.Adj x (e i) := by
    fin_cases i
    · exact ⟨fun _ => (external_adj G h0 hx).mpr rfl, fun _ => rfl⟩
    · exact ⟨fun h => Bool.noConfusion h, fun h => (hxy ((external_adj G h1 hx).mp h)).elim⟩
    · exact ⟨fun h => Bool.noConfusion h, fun h => (hxz ((external_adj G h2 hx).mp h)).elim⟩
  have he4 : Realizes G e4 firstDistinctDiagram :=
    realizes_appendRow G he x hx _ hxrow
  have hy4 : y ∉ Set.range e4 := by
    change y ∉ Set.range (appendName e x hx)
    rw [range_appendName]
    exact fun h => h.elim (fun eq => hxy eq.symm) hy
  let e5 := appendName e4 y hy4
  let b := decide (G.Adj y x)
  have hyrow (i : Fin 4) :
      (![false, true, false, b] : Fin 4 → Bool) i = true ↔ G.Adj y (e4 i) := by
    fin_cases i
    · exact ⟨fun h => Bool.noConfusion h, fun h => (hxy ((external_adj G h0 hy).mp h).symm).elim⟩
    · exact ⟨fun _ => (external_adj G h1 hy).mpr rfl, fun _ => rfl⟩
    · exact ⟨fun h => Bool.noConfusion h, fun h => (hyz ((external_adj G h2 hy).mp h)).elim⟩
    · exact decide_eq_true_iff
  have he5 : Realizes G e5 (distinctDiagram b) :=
    realizes_appendRow G he4 y hy4 _ hyrow
  have hSeal (i : Fin 5) (hi : exposed5 i = some false) :
      G.neighborSet (e5 i) ⊆ Set.range e5 := by
    rcases exposed5_false i hi with rfl | rfl
    · exact exact_row_sealed G (i := 0) (j := 1) (k := 2) (l := 3) h0
    · exact exact_row_sealed G (i := 1) (j := 0) (k := 2) (l := 4) h1
  have hreply := exposed_reply G 1 he5 extends_exposed5 (checked_distinct b) exposed5_total hSeal
  simpa only [e5, e4, position_append_none,
    show (1 : Fin 5) = (1 : Fin 4).castSucc from rfl,
    show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, appendName_castSucc] using hreply

end TenChallenges.Continuation.NamedPositions.TriangleReplies


namespace TenChallenges.Continuation.AdjacentPositions

open NamedPositions NamedPositions.TriangleReplies
open _root_.Continuation.TC10

variable {V : Type u} (G : SimpleGraph V)

private theorem fresh_triple {a b c x : V} {hab : a ≠ b} {hac : a ≠ c} {hbc : b ≠ c}
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c) : x ∉ Set.range (triple a b c hab hac hbc) := by
  rintro ⟨i, hi⟩
  fin_cases i
  · exact hx.1 hi.symm
  · exact hx.2.1 hi.symm
  · exact hx.2.2 hi.symm

/-- Reply at the third vertex when it shares its external neighbour with the
first vertex. -/
theorem shared_reply {f : V → Option Bool} {a b c s : V} (h : PairState f a b)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hs : s ≠ a ∧ s ≠ b ∧ s ≠ c)
    (ra : G.neighborSet a = {b, c, s}) (rc : G.neighborSet c = {a, b, s}) :
    Reply.{u,v} G f c := by
  let e := triple a c b (G.ne_of_adj hac) (G.ne_of_adj hab) (G.ne_of_adj hbc).symm
  have he : Realizes G e tri3 := realizes_triangle G hac hab hbc.symm
  have hs' : s ∉ Set.range e := fresh_triple ⟨hs.1, hs.2.2, hs.2.1⟩
  have hExt : Extends f (position e beforeExposedTriangle) :=
    h.extends (position_name e beforeExposedTriangle 0) (position_name e beforeExposedTriangle 2)
  exact reply_from_extension G hExt (cubic_triangle_shared_exposed_reply G he hs'
    (ra.trans (Set.insert_comm b c ({s} : Set V))) rc)

/-- Reply at the third vertex when all three external neighbours are distinct. -/
theorem distinct_reply {f : V → Option Bool} {a b c s t r : V} (h : PairState f a b)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hs : s ≠ a ∧ s ≠ b ∧ s ≠ c) (ht : t ≠ a ∧ t ≠ b ∧ t ≠ c)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r)
    (ra : G.neighborSet a = {b, c, s}) (rc : G.neighborSet c = {a, b, t})
    (rb : G.neighborSet b = {a, c, r}) :
    Reply.{u,v} G f c := by
  let e := triple a c b (G.ne_of_adj hac) (G.ne_of_adj hab) (G.ne_of_adj hbc).symm
  have he : Realizes G e tri3 := realizes_triangle G hac hab hbc.symm
  have hs' : s ∉ Set.range e := fresh_triple ⟨hs.1, hs.2.2, hs.2.1⟩
  have ht' : t ∉ Set.range e := fresh_triple ⟨ht.1, ht.2.2, ht.2.1⟩
  have hExt : Extends f (position e beforeExposedTriangle) :=
    h.extends (position_name e beforeExposedTriangle 0) (position_name e beforeExposedTriangle 2)
  exact reply_from_extension G hExt (cubic_triangle_distinct_exposed_reply G he hs' ht' hst hsr htr
    (ra.trans (Set.insert_comm b c ({s} : Set V))) rc rb)

end TenChallenges.Continuation.AdjacentPositions

end

-- Source: Continuation/UnfriendlyExceptionalCubic.lean
section

/-! # The cubic triangle with a shared external neighbour at the first edge -/

set_option autoImplicit false

universe u v

section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TenChallenges.Continuation.NamedPositions.ExceptionalCubic

open TriangleReplies

/-- The names are the matching ends, the minority end, then their two exterior neighbours. -/
def exceptionalMatrix (st : Bool) : Edges 5 :=
  ![![false, true, true, true, false],
    ![true, false, true, false, true],
    ![true, true, false, true, false],
    ![true, false, true, false, st],
    ![false, true, false, st, false]]

def boundsAtS (st : Bool) : Fin 5 → ℕ :=
  if st then largeAt 3 else fun _ => 2

theorem checked_repeats : ∀ st : Bool, ∀ i : Fin 5, i.val < 3 →
    CheckedPlan (exceptionalMatrix st) (fun _ => 2) (flags {0, 1, 2}) 2 TriangleReplies.start5 i
      (singletonPlan (exceptionalMatrix st) (fun _ => 2) 2 TriangleReplies.start5) := by
  decide +kernel

theorem checked_s : ∀ st : Bool,
    let A := exceptionalMatrix st
    let p := triColours5 (some true) none
    let lo := boundsAtS st
    CheckedPlan A lo (flags {0, 1, 2}) 2 p 3 (singletonPlan A lo 2 p) := by
  decide +kernel

theorem checked_t_without_st :
    let A := exceptionalMatrix false
    let p := triColours5 none (some true)
    CheckedPlan A (fun _ => 2) (flags {0, 1, 2}) 2 p 4
      (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

theorem checked_t_with_witness : ∀ zt : Bool,
    let A := appendRow (exceptionalMatrix true) ![false, false, false, true, zt]
    let p := triColours6 none (some true) none
    let extra (i : Fin 6) :=
      if i = 3 then some (triColours6 (some true) (some true) (some false)) else none
    CheckedPlan A (fun _ => 2) (flags {0, 1, 2}) 2 p 4
      (singletonPlan A (fun _ => 2) 2 p extra) := by
  decide +kernel

theorem checked_outside : ∀ st xs xt : Bool,
    let A := appendRow (exceptionalMatrix st) ![false, false, false, xs, xt]
    let p := triColours6 none none (some false)
    CheckedPlan A (fun _ => 2) (flags {0, 1, 2}) 2 p 5
      (singletonPlan A (fun _ => 2) 2 p) := by
  decide +kernel

end TenChallenges.Continuation.NamedPositions.ExceptionalCubic

end

namespace TenChallenges.Continuation.NamedPositions.ExceptionalCubic

open TriangleReplies
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

private theorem seals_after_append {e : Fin 5 ↪ V} {x : V} (hx : x ∉ Set.range e)
    (hs : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), G.neighborSet (e i) ⊆ Set.range e)
    (i : Fin 6) (hi : i ∈ ({0, 1, 2} : Finset (Fin 6))) :
    G.neighborSet (appendName e x hx i) ⊆ Set.range (appendName e x hx) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact (hs 0 (by simp)).trans (old_names_subset_append hx)
  · exact (hs 1 (by simp)).trans (old_names_subset_append hx)
  · exact (hs 2 (by simp)).trans (old_names_subset_append hx)

private theorem realizes_outside {e : Fin 5 ↪ V} {st : Bool}
    (he : Realizes G e (exceptionalMatrix st))
    (hs : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), G.neighborSet (e i) ⊆ Set.range e)
    (x : V) (hx : x ∉ Set.range e) :
    ∃ xs xt : Bool, (xs = true ↔ G.Adj x (e 3)) ∧
      Realizes G (appendName e x hx) (appendRow (exceptionalMatrix st) ![false, false, false, xs, xt]) := by
  classical
  let r (i : Fin 5) := decide (G.Adj x (e i))
  have hr : ∀ i, r i = true ↔ G.Adj x (e i) := fun _ => decide_eq_true_iff
  have hrzero (i : Fin 5) (hi : i ∈ ({0, 1, 2} : Finset (Fin 5))) : r i = false :=
    decide_eq_false (fun ha : G.Adj x (e i) => hx (hs i hi ha.symm))
  refine ⟨r 3, r 4, hr 3, ?_⟩
  have hr' : r = ![false, false, false, r 3, r 4] := by
    funext i
    fin_cases i <;> first | rfl | exact hrzero _ (by decide)
  exact hr' ▸ realizes_appendRow G he x hx r hr

private theorem t_reply {e : Fin 5 ↪ V} {st : Bool}
    (he : Realizes G e (exceptionalMatrix st))
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hs : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), G.neighborSet (e i) ⊆ Set.range e)
    (hst : st = false ∨ 4 ≤ #(G.neighborSet (e 3))) :
    ReplyTwo.{u,v} G (position e TriangleReplies.start5) (e 4) := by
  cases st
  · exact reply_of_table G he hmin (fun i => hmin (e i)) hs
      (extends_start5 none (some true)) checked_t_without_st
  · have hfour := hst.resolve_left (by decide)
    have hnamed : namedDegree (exceptionalMatrix true) 3 = 3 := by decide
    obtain ⟨z, hsz, hz⟩ := exists_freshNeighbor_of_degree_four G he 3 hnamed hfour
    obtain ⟨zs, zt, hzAdj, he6⟩ := realizes_outside G he hs z hz
    rw [hzAdj.mpr hsz.symm] at he6
    exact project_append_reply G hz TriangleReplies.start5 4
      (reply_of_table G he6 hmin (fun i => hmin (appendName e z hz i))
        (seals_after_append G hz hs) (extends_start6 none (some true) none)
        (checked_t_with_witness zt))

private theorem s_reply {e : Fin 5 ↪ V} {st : Bool}
    (he : Realizes G e (exceptionalMatrix st))
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hs : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), G.neighborSet (e i) ⊆ Set.range e)
    (hst : st = false ∨ 4 ≤ #(G.neighborSet (e 3))) :
    ReplyTwo.{u,v} G (position e TriangleReplies.start5) (e 3) := by
  have hlo (i : Fin 5) : (boundsAtS st i : Cardinal) ≤ #(G.neighborSet (e i)) := by
    cases st
    · exact hmin (e i)
    · exact bounds_largeAt G (e := e) hmin 3 (hst.resolve_left (by decide)) i
  exact reply_of_table G he hmin hlo hs (extends_start5 (some true) none) (checked_s st)

private theorem outside_reply {e : Fin 5 ↪ V} {st : Bool}
    (he : Realizes G e (exceptionalMatrix st))
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hs : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), G.neighborSet (e i) ⊆ Set.range e)
    (x : V) (hx : x ∉ Set.range e) :
    ReplyTwo.{u,v} G (position e TriangleReplies.start5) x := by
  obtain ⟨xs, xt, _, he6⟩ := realizes_outside G he hs x hx
  have hres := reply_of_table G he6 hmin (fun i => hmin (appendName e x hx i))
    (seals_after_append G hx hs) (extends_start6 none none (some false))
    (checked_outside st xs xt)
  simpa only [start6, position_append_none, show (5 : Fin 6) = Fin.last 5 from rfl,
    appendName_last] using hres

/-- The cubic triangle with the minority end sharing an exterior neighbour
with one matching end wins three rounds if its two exterior neighbours are
nonadjacent or the shared neighbour has degree at least four. -/
theorem exceptional_cubic_triangle_wins_three {e : Fin 5 ↪ V} {st : Bool}
    (he : Realizes G e (exceptionalMatrix st))
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (ha : G.neighborSet (e 0) ⊆ Set.range e) (hc : G.neighborSet (e 1) ⊆ Set.range e)
    (hb : G.neighborSet (e 2) ⊆ Set.range e) (hst : st = false ∨ 4 ≤ #(G.neighborSet (e 3))) :
    PartitionerWins G (position e TriangleReplies.start5) (3 : Ordinal.{v}) := by
  have hs (i : Fin 5) (hi : i ∈ ({0, 1, 2} : Finset (Fin 5))) :
      G.neighborSet (e i) ⊆ Set.range e := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ha
    · exact hc
    · exact hb
  rw [PartitionerWins]
  intro x β hβ
  suffices h : ReplyTwo.{u,v} G (position e TriangleReplies.start5) x by
    obtain ⟨g, hg, hw⟩ := h
    have hle : β ≤ 2 := Order.lt_add_one_iff.mp
      (by simpa only [two_add_one_eq_three] using hβ)
    exact ⟨g, hg, _root_.Continuation.TC10.wins_mono G hle hw⟩
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    by_cases hi : i.val < 3
    · exact reply_of_table G he hmin (fun j => hmin (e j)) hs (fun _ _ h => h)
        (checked_repeats st i hi)
    · fin_cases i
      · exact (hi (by decide)).elim
      · exact (hi (by decide)).elim
      · exact (hi (by decide)).elim
      · exact s_reply G he hmin hs hst
      · exact t_reply G he hmin hs hst
  · exact outside_reply G he hmin hs x hx

theorem exceptional_position_append (e : Fin 3 ↪ V) (s : V) (hs : s ∉ Set.range e)
    (t : V) (ht : t ∉ Set.range (appendName e s hs)) :
    position (appendName (appendName e s hs) t ht) TriangleReplies.start5 = position e triStart := by
  simp only [TriangleReplies.start5, start4, position_append_none]

end TenChallenges.Continuation.NamedPositions.ExceptionalCubic

namespace TenChallenges.Continuation.AdjacentPositions

open NamedPositions
open NamedPositions.ExceptionalCubic
open NamedPositions.TriangleReplies
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- A valid third response for the cubic triangle with a shared exterior
neighbour at the original two vertices. -/
theorem exceptional_reply {f : V → Option Bool} {a b c s t : V}
    (h : PairState f a b) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hs : s ≠ a ∧ s ≠ b ∧ s ≠ c) (ht : t ≠ a ∧ t ≠ b ∧ t ≠ c) (hst : s ≠ t)
    (ra : G.neighborSet a = {b, c, s}) (rb : G.neighborSet b = {a, c, s})
    (rc : G.neighborSet c = {a, b, t})
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w))
    (hSafe : ¬ G.Adj s t ∨ 4 ≤ #(G.neighborSet s)) :
    Reply.{u,v} G f c := by
  classical
  have hab' := G.ne_of_adj hab
  have hac' := G.ne_of_adj hac
  have hbc' := G.ne_of_adj hbc
  let e : Fin 5 ↪ V := ⟨![a, c, b, s, t], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]⟩
  let st := decide (G.Adj s t)
  have has : G.Adj a s := by
    rw [← SimpleGraph.mem_neighborSet, ra]
    simp
  have hbs : G.Adj b s := by
    rw [← SimpleGraph.mem_neighborSet, rb]
    simp
  have hct : G.Adj c t := by
    rw [← SimpleGraph.mem_neighborSet, rc]
    simp
  have hat : ¬ G.Adj a t := by
    rw [← SimpleGraph.mem_neighborSet, ra]
    simp [ht.2.1, ht.2.2, hst.symm]
  have hbt : ¬ G.Adj b t := by
    rw [← SimpleGraph.mem_neighborSet, rb]
    simp [ht.1, ht.2.2, hst.symm]
  have hcs : ¬ G.Adj c s := by
    rw [← SimpleGraph.mem_neighborSet, rc]
    simp [hs.1, hs.2.1, hst]
  have he : Realizes G e (exceptionalMatrix st) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact decide_eq_true_iff
      | exact (decide_eq_true_iff (p := G.Adj s t)).trans (G.adj_comm s t)
      | exact ⟨fun h => Bool.noConfusion h, fun h => (G.irrefl h).elim⟩
      | exact ⟨fun _ => hab, fun _ => rfl⟩
      | exact ⟨fun _ => hab.symm, fun _ => rfl⟩
      | exact ⟨fun _ => hac, fun _ => rfl⟩
      | exact ⟨fun _ => hac.symm, fun _ => rfl⟩
      | exact ⟨fun _ => hbc, fun _ => rfl⟩
      | exact ⟨fun _ => hbc.symm, fun _ => rfl⟩
      | exact ⟨fun _ => has, fun _ => rfl⟩
      | exact ⟨fun _ => has.symm, fun _ => rfl⟩
      | exact ⟨fun _ => hbs, fun _ => rfl⟩
      | exact ⟨fun _ => hbs.symm, fun _ => rfl⟩
      | exact ⟨fun _ => hct, fun _ => rfl⟩
      | exact ⟨fun _ => hct.symm, fun _ => rfl⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hat h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hat h.symm).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hbt h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hbt h.symm).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hcs h).elim⟩
      | exact ⟨fun h => Bool.noConfusion h, fun h => (hcs h.symm).elim⟩
  have hsealA : G.neighborSet (e 0) ⊆ Set.range e := by
    change G.neighborSet a ⊆ Set.range e
    rw [ra, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨2, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩⟩
  have hsealB : G.neighborSet (e 2) ⊆ Set.range e := by
    change G.neighborSet b ⊆ Set.range e
    rw [rb, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩⟩
  have hsealC : G.neighborSet (e 1) ⊆ Set.range e := by
    change G.neighborSet c ⊆ Set.range e
    rw [rc, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨0, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩⟩
  have hst' : st = false ∨ 4 ≤ #(G.neighborSet (e 3)) :=
    hSafe.imp (fun hn => decide_eq_false hn) id
  exact named_reply G he TriangleReplies.start5 1 (h.extends (position_name e TriangleReplies.start5 0) (position_name e TriangleReplies.start5 2))
    (checked_repeats st 1 (by decide)).1
    (exceptional_cubic_triangle_wins_three G he hmin hsealA hsealC hsealB hst')

end TenChallenges.Continuation.AdjacentPositions

end

-- Source: Continuation/UnfriendlySixRounds.lean
section

/-! # Six rounds of the unfriendly partition game on every simple graph -/

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.SixRounds

open NamedPositions AdjacentPositions
open _root_.Continuation.TC10
open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

private theorem exceptional_safe {a b c s t : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hs : s ≠ a ∧ s ≠ b ∧ s ≠ c) (ht : t ≠ a ∧ t ≠ b ∧ t ≠ c) (hst : s ≠ t)
    (ra : G.neighborSet a = {b,c,s}) (rb : G.neighborSet b = {a,c,s})
    (rc : G.neighborSet c = {a,b,t}) (hTrap : ¬ HasTrap G a b) :
    ¬ G.Adj s t ∨ 4 ≤ #(G.neighborSet s) := by
  by_cases hadj : G.Adj s t
  · apply Or.inr
    by_contra hdeg
    have hle : #(G.neighborSet s) ≤ 3 := Cardinal.lt_natCast_add_one_iff.mp (by
      simpa only [Nat.cast_ofNat, three_add_one_eq_four] using lt_of_not_ge hdeg)
    have hcard : (G.neighborSet s).encard ≤ 3 := by
      simpa only [Set.toENat_cardinalMk, Cardinal.toENat_ofNat] using Cardinal.enat_gc.monotone_u hle
    have has : G.Adj a s := show s ∈ G.neighborSet a from ra.symm ▸ (by simp)
    have hbs : G.Adj b s := show s ∈ G.neighborSet b from rb.symm ▸ (by simp)
    have rs := row_from_three (s := G.neighborSet s) hab.ne ht.1.symm ht.2.1.symm
      has.symm hbs.symm hadj hcard
    exact hTrap (trap_of_rows G hab.ne ht.1.symm ht.2.1.symm
      ⟨hac.ne.symm,hbc.ne.symm,ht.2.2.symm⟩ ⟨hs.1,hs.2.1,hst⟩ hs.2.2.symm ra rb rc rs)
  · exact Or.inl hadj

private theorem triangle_reply {a b c : V} {f : V → Option Bool} (h : PairState f a b)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) (hTrap : ¬ HasTrap G a b) :
    Reply.{u,v} G f c := by
  rcases triangle_one_side G h hab hac hbc hmin with hw | ⟨da,dc⟩
  · exact hw
  rcases triangle_one_side G h.flip hab.symm hbc hac hmin with hw | ⟨db,_⟩
  · exact reply_of_complement G hw
  obtain ⟨s,hsa,hsb,hsc,ra⟩ := cubic_external G hab hac hbc.ne da
  obtain ⟨r,hrb,hra,hrc,rb⟩ := cubic_external G hab.symm hbc hac.ne db
  obtain ⟨t,htc,hta,htb,rc⟩ := cubic_external G hac.symm hbc.symm hab.ne dc
  rcases eq_or_ne t s with rfl | hts
  · exact shared_reply G h hab hac hbc ⟨hsa,hsb,hsc⟩ ra rc
  rcases eq_or_ne t r with rfl | htr
  · exact reply_of_complement G (shared_reply G h.flip hab.symm hbc hac
      ⟨hrb,hra,hrc⟩ rb (rc.trans (Set.insert_comm a b _)))
  rcases eq_or_ne r s with rfl | hrs
  · exact exceptional_reply G h hab hac hbc ⟨hsa,hsb,hsc⟩ ⟨hta,htb,htc⟩ hts.symm ra rb rc hmin
      (exceptional_safe G hab hac hbc ⟨hsa,hsb,hsc⟩ ⟨hta,htb,htc⟩ hts.symm ra rb rc hTrap)
  · exact distinct_reply G h hab hac hbc ⟨hsa,hsb,hsc⟩ ⟨hta,htb,htc⟩ hts.symm hrs.symm htr ra rc rb

private theorem adjacent_response {a b : V} (hab : G.Adj a b)
    (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    ∃ f, IsLegalResponse G (first a) f b ∧ PartitionerWins G f (4 : Ordinal.{v}) := by
  classical
  by_cases hTrap : HasTrap G a b
  · obtain ⟨T,rfl,rfl⟩ := hTrap
    exact T.response
  let f := second G a b
  obtain ⟨hLegal,hReady⟩ := second_legal_ready G a b
  have ha : f a = some false := by simp [f,second,first,Function.update_of_ne hab.ne]
  have hb : f b = some true := by simp [f,second,hab]
  have hpair : PairState f a b := ⟨ha,hb, fun x hx => Classical.byContradiction fun hn =>
    hx (by simp [f,second,first,Function.update_of_ne (not_or.mp hn).1,
      Function.update_of_ne (not_or.mp hn).2,emptyPartition])⟩
  refine ⟨f,hLegal,?_⟩
  rw [PartitionerWins]
  intro c β hβ
  suffices hr : Reply.{u,v} G f c by
    obtain ⟨g,hg,hw⟩ := hr
    exact ⟨g,hg,wins_mono G (Order.lt_add_one_iff.mp
      (by simpa only [three_add_one_eq_four] using hβ)) hw⟩
  by_cases hc : f c = none
  · have hac : a ≠ c := fun he => Option.some_ne_none false (ha.symm.trans (he.symm ▸ hc))
    have hbc : b ≠ c := fun he => Option.some_ne_none true (hb.symm.trans (he.symm ▸ hc))
    by_cases ac : G.Adj a c
    · by_cases bc : G.Adj b c
      · exact triangle_reply G hpair hab ac bc hmin hTrap
      · exact star_reply G hpair hab ac hbc bc
    · by_cases bc : G.Adj b c
      · exact reply_of_complement G (star_reply G hpair.flip hab.symm bc hac ac)
      · exact isolated_reply G hpair hab hac hbc ac bc hmin hTrap
  · obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hc
    exact ⟨f,⟨fun _ _ h => h,hLegal.2.1,ready_stable G hReady c d hd⟩,
      _root_.Continuation.TC10R5.ready_wins_three G hLegal.2.1 hReady⟩

private theorem first_wins_five (a : V) (hmin : ∀ w, (2 : Cardinal) ≤ #(G.neighborSet w)) :
    PartitionerWins G (first a) (5 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro b β hβ
  suffices h : ∃ f, IsLegalResponse G (first a) f b ∧ PartitionerWins G f (4 : Ordinal.{v}) by
    obtain ⟨f,hf,hw⟩ := h
    exact ⟨f,hf,wins_mono G (Order.lt_add_one_iff.mp
      (by simpa only [show (4 : Ordinal.{v}) + 1 = 5 from rfl] using hβ)) hw⟩
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨first a,⟨fun _ _ h => h,(first_legal G a).2⟩,SealedBlock.first_wins_four G a⟩
  by_cases hadj : G.Adj a b
  · exact adjacent_response G hadj hmin
  · exact ⟨second G a b,(second_legal_ready G a b).1,second_nonadjacent_wins_four G hab hadj hmin⟩

/-- On every simple graph, Partitioner wins from the empty position with six
rounds on the ordinal clock. The vertex and clock universes are independent. -/
theorem wins_six : PartitionerWins G (emptyPartition V) (6 : Ordinal.{v}) := by
  apply TwoCore.partitionerWins_of_twoCore G
  rw [PartitionerWins]
  intro a β hβ
  exact ⟨first a,first_legal _ a,wins_mono _ (Order.lt_add_one_iff.mp
    (by simpa only [show (5 : Ordinal.{v}) + 1 = 6 from rfl] using hβ))
    (first_wins_five _ a (TwoCore.core_degree G))⟩

end TenChallenges.Continuation.SixRounds

end

universe u v

theorem solution : TenChallenges.statement_10.{u, v} 6 := by
  intro V _ G
  exact TenChallenges.Continuation.SixRounds.wins_six G

#print axioms solution
