-- Prove2me | solution 1 for TenChallenges.challenge_10_r5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:44:05.634204+00:00
-- url     : https://prove2.me/submissions/620ddeca-ba6d-4489-8a4d-9ed291cdf358

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Basic

universe u v

set_option linter.all false


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

open scoped Cardinal

namespace Continuation.TC10R5Helpers


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

set_option linter.all false


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

set_option linter.all false

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


theorem solution : TenChallenges.statement_10.{u, v} 5 := by
  intro W _ H
  exact Continuation.TC10R5.win_five H

#print axioms solution
