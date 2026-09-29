-- Prove2me | solution 1 for WeierstrassCurve.apOfModel_ne_succ_and_ne_neg_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/adcfa6b8-d725-59f2-bb7d-e3e8a11874a7

import Mathlib.Algebra.Field.ZMod
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine mk.injEq a₃ a₁ mk a₄ a₂ a₆ reduction toAffine Affine.equation_iff card traceOfFrobenius reductionMod apOfModel"
p2m_open "WeierstrassCurve"

namespace StripS6

variable {F : Type} [Field F] (W : WeierstrassCurve F)

noncomputable def yPoly (x : F) : F[X] :=
  C (1 : F) * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))

theorem natDegree_yPoly (x : F) : (yPoly W x).natDegree = 2 :=
  natDegree_quadratic one_ne_zero

theorem isRoot_yPoly_iff (x y : F) : (yPoly W x).IsRoot y ↔ W.toAffine.Equation x y := by
  rw [Affine.equation_iff, yPoly, IsRoot.def]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  constructor <;> intro h <;> linear_combination h

theorem yPoly_ne_zero (x : F) : yPoly W x ≠ 0 := by
  intro h
  have h2 := natDegree_yPoly W x
  rw [h, natDegree_zero] at h2
  exact absurd h2 (by norm_num)

theorem card_fiber_le_two (x : F) : Nat.card {y : F // W.toAffine.Equation x y} ≤ 2 := by
  classical
  let g : {y : F // W.toAffine.Equation x y} → ((yPoly W x).roots.toFinset : Finset F) := fun y =>
    ⟨y.1, by rw [Multiset.mem_toFinset, mem_roots (yPoly_ne_zero W x), isRoot_yPoly_iff]; exact y.2⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  calc Nat.card {y : F // W.toAffine.Equation x y}
      ≤ Nat.card ((yPoly W x).roots.toFinset : Finset F) := Nat.card_le_card_of_injective g hg
    _ = (yPoly W x).roots.toFinset.card := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (yPoly W x).roots := Multiset.toFinset_card_le _
    _ ≤ (yPoly W x).natDegree := card_roots' _
    _ = 2 := natDegree_yPoly W x

theorem card_point_le [Fintype F] : W.card ≤ 2 * Nat.card F + 1 := by
  classical
  let f : W.toAffine.Point → Option (Σ x : F, {y : F // W.toAffine.Equation x y}) := fun P =>
    match P with
    | .zero => none
    | .some (x := x) (y := y) h => some ⟨x, ⟨y, ((W.toAffine.nonsingular_iff' x y).mp h).1⟩⟩
  have hf : Function.Injective f := by
    intro P Q hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some _ => simp [f] at hPQ
    | some hP =>
      cases Q with
      | zero => simp [f] at hPQ
      | some hQ =>
        simp only [f, Option.some.injEq, Sigma.mk.injEq] at hPQ
        obtain ⟨rfl, hy⟩ := hPQ
        have hy' : _ = _ := congrArg Subtype.val (eq_of_heq hy)
        simp only at hy'
        subst hy'
        rfl
  have h1 : W.card ≤ Nat.card (Option (Σ x : F, {y : F // W.toAffine.Equation x y})) :=
    Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Option (Σ x : F, {y : F // W.toAffine.Equation x y}))
      = Nat.card (Σ x : F, {y : F // W.toAffine.Equation x y}) + 1 := by
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card (Σ x : F, {y : F // W.toAffine.Equation x y})
      = ∑ x : F, Nat.card {y : F // W.toAffine.Equation x y} := Nat.card_sigma
  have h4 : ∑ x : F, Nat.card {y : F // W.toAffine.Equation x y} ≤ ∑ _x : F, 2 :=
    Finset.sum_le_sum fun x _ => card_fiber_le_two W x
  have h5 : ∑ _x : F, (2 : ℕ) = 2 * Nat.card F := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card]
  omega

theorem one_le_card [Finite F] : 1 ≤ W.card := by
  have : Nonempty W.toAffine.Point := ⟨.zero⟩
  exact Nat.card_pos

end StripS6

end WeierstrassCurve

theorem solution (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) :
    WeierstrassCurve.apOfModel W q ≠ (q : ℤ) + 1 ∧ WeierstrassCurve.apOfModel W q ≠ -((q : ℤ) + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (ZMod q) = q := Nat.card_zmod q
  have hle := WeierstrassCurve.StripS6.card_point_le (W.reductionMod q)
  have hge := WeierstrassCurve.StripS6.one_le_card (W.reductionMod q)
  rw [hcard] at hle
  unfold WeierstrassCurve.apOfModel WeierstrassCurve.traceOfFrobenius
  rw [hcard]
  constructor <;> intro h <;> omega

end S_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ
end P2MW
export P2MW.S_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ (solution)
