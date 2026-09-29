-- Prove2me | solution 1 for WeierstrassCurve.eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d4fd1e19-4603-5bb6-b341-f944cabf59e6

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Theorems.Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map b₂ Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.some.inj toAffine Affine.Point b₆ Affine.equation_iff Affine.Point.neg_some b₄ veluX veluGx veluGy veluT veluU veluU_eq_Ψ₂Sq_eval veluGy_eq_zero_of_negY_eq veluQuotient oddOrderSummingSet mem_oddOrderSummingSet veluY velu_map_equation_of_oddOrderSummingSet"
p2m_open "WeierstrassCurve"

section Helpers

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
lemma s18c_exists_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = Point.some x y h ∧
      P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

lemma s18c_two_nsmul_eq_zero_iff_Y_eq_negY {x y : F} (h : W.toAffine.Nonsingular x y) :
    2 • (Point.some x y h : W.toAffine.Point) = 0 ↔ y = W.toAffine.negY x y := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some]
  exact ⟨fun hP => (Affine.Point.some.inj hP).right,
    fun hy => by simp only [Affine.Point.some.injEq]; exact ⟨trivial, hy⟩⟩

lemma s18c_veluGy_ne_zero_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    W.veluGy x y ≠ 0 := by
  intro h0
  apply h2
  apply (s18c_two_nsmul_eq_zero_iff_Y_eq_negY h).mpr
  have hkey : W.toAffine.negY x y = y + W.veluGy x y := by
    simp only [Affine.negY, veluGy]; ring
  rw [hkey, h0, add_zero]

variable {Q : W.toAffine.Point} {p : ℕ}

theorem s18c_eval_Ψ₂Sq_ne_zero_of_mem_oddOrderSummingSet {n : ℕ}
    (hord : addOrderOf Q = 2 * n + 1) {P : F × F}
    (hP : P ∈ W.oddOrderSummingSet Q n) : W.Ψ₂Sq.eval P.1 ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  have hndvd : ¬ (2 * n + 1) ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hndvd2 : ¬ (2 * n + 1) ∣ 2 * k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hne : k • Q ≠ 0 := fun h => hndvd (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)
  have h2k : (2 * k) • Q ≠ 0 := fun h =>
    hndvd2 (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)
  obtain ⟨x, y, h, heq, hcoords⟩ := s18c_exists_some_of_ne_zero hne
  have hPxy : P = (x, y) := by rw [← hkP, hcoords]
  subst hPxy
  have h2ns : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0 := by
    intro h0; apply h2k; rw [mul_nsmul', heq, h0]
  rw [← W.veluU_eq_Ψ₂Sq_eval h.left]
  simpa only [veluU] using pow_ne_zero 2 (s18c_veluGy_ne_zero_of_two_nsmul_ne_zero h h2ns)

omit [DecidableEq F] in

private lemma s18c_veluY_summand_negY (x y : F) (A : F × F) :
    W.veluU A.1 A.2 * (2 * W.toAffine.negY x y + W.a₁ * x + W.a₃) / (x - A.1) ^ 3
      + W.veluT A.1 A.2 * (W.a₁ * (x - A.1) + W.toAffine.negY x y - A.2) / (x - A.1) ^ 2
      + (W.a₁ * W.veluU A.1 A.2 - W.veluGx A.1 A.2 * W.veluGy A.1 A.2) / (x - A.1) ^ 2
    = W.a₁ * (W.veluT A.1 A.2 / (x - A.1) + W.veluU A.1 A.2 / (x - A.1) ^ 2)
      - (W.veluU A.1 A.2 * (2 * y + W.a₁ * x + W.a₃) / (x - A.1) ^ 3
        + W.veluT A.1 A.2 * (W.a₁ * (x - A.1) + y - A.2) / (x - A.1) ^ 2
        + (W.a₁ * W.veluU A.1 A.2 - W.veluGx A.1 A.2 * W.veluGy A.1 A.2) / (x - A.1) ^ 2) := by
  rcases eq_or_ne x A.1 with h | h
  · simp [h, sub_self]
  · have hd : x - A.1 ≠ 0 := sub_ne_zero.mpr h
    simp only [veluT, veluU, veluGx, veluGy, Affine.negY]
    field_simp
    ring

omit [DecidableEq F] in

lemma s18c_veluY_negY (S : Finset (F × F)) (x y : F) :
    W.veluY S x (W.toAffine.negY x y)
      = (W.veluQuotient S).toAffine.negY (W.veluX S x) (W.veluY S x y) := by
  simp only [veluY, veluX]
  rw [Finset.sum_congr rfl fun A _ => s18c_veluY_summand_negY (W := W) x y A,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Affine.negY, veluQuotient]
  ring

omit [DecidableEq F] in

theorem s18c_veluQuotient_eval_Ψ₂Sq_veluX_eq_zero_of_mapeq {S : Finset (F × F)} {r s : F}
    (hy : s = W.toAffine.negY r s)
    (hmapeq : (W.veluQuotient S).toAffine.Equation (W.veluX S r) (W.veluY S r s)) :
    (W.veluQuotient S).Ψ₂Sq.eval (W.veluX S r) = 0 := by
  have hneg' : W.veluY S r s
      = (W.veluQuotient S).toAffine.negY (W.veluX S r) (W.veluY S r s) := by
    nth_rewrite 1 [hy]
    exact s18c_veluY_negY S r s
  have hgy' : (W.veluQuotient S).veluGy (W.veluX S r) (W.veluY S r s) = 0 :=
    (W.veluQuotient S).veluGy_eq_zero_of_negY_eq hneg'.symm
  rw [← (W.veluQuotient S).veluU_eq_Ψ₂Sq_eval hmapeq]
  simp [veluU, hgy']

variable (W) in

private def _root_.WeierstrassCurve.s18c_twoTorsionY (x : F) : F := -(W.a₁ * x + W.a₃) / 2

p2m_export "WeierstrassCurve" "s18c_twoTorsionY"
omit [DecidableEq F] in
lemma s18c_twoTorsionY_eq_negY (h2 : (2 : F) ≠ 0) (x : F) :
    W.s18c_twoTorsionY x = W.toAffine.negY x (W.s18c_twoTorsionY x) := by
  rw [s18c_twoTorsionY, Affine.negY]
  field_simp
  ring

omit [DecidableEq F] in
lemma s18c_equation_twoTorsionY_of_eval (h2 : (2 : F) ≠ 0) {x : F}
    (h : W.Ψ₂Sq.eval x = 0) : W.toAffine.Equation x (W.s18c_twoTorsionY x) := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = (2 : F) ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2
  have key : (4 : F) * (W.s18c_twoTorsionY x ^ 2 + W.a₁ * x * W.s18c_twoTorsionY x +
      W.a₃ * W.s18c_twoTorsionY x - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) =
      -(W.Ψ₂Sq.eval x) := by
    rw [s18c_twoTorsionY, Ψ₂Sq, b₂, b₄, b₆]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    field_simp
    ring
  rw [Affine.equation_iff]
  have h0 : (4 : F) * (W.s18c_twoTorsionY x ^ 2 + W.a₁ * x * W.s18c_twoTorsionY x +
      W.a₃ * W.s18c_twoTorsionY x - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
    rw [key, h, _root_.neg_zero]
  have := (mul_eq_zero.mp h0).resolve_left h4
  linear_combination this

end Helpers

end WeierstrassCurve

end

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {r : L} (hr : W.Ψ₂Sq.eval r = 0) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Ψ₂Sq.eval
      (W.veluX (W.oddOrderSummingSet Q n) r) = 0 := by
  set S := W.oddOrderSummingSet Q n with hS

  have heqt : W.toAffine.Equation r (W.s18c_twoTorsionY r) :=
    WeierstrassCurve.s18c_equation_twoTorsionY_of_eval h2 hr

  have hav : ∀ A ∈ S, r ≠ A.1 := fun A hA hc =>
    WeierstrassCurve.s18c_eval_Ψ₂Sq_ne_zero_of_mem_oddOrderSummingSet (W := W) hQ hA (hc ▸ hr)

  have hmapeq := W.velu_map_equation_of_oddOrderSummingSet h2 n Q hQ heqt hav

  exact WeierstrassCurve.s18c_veluQuotient_eval_Ψ₂Sq_veluX_eq_zero_of_mapeq
    (WeierstrassCurve.s18c_twoTorsionY_eq_negY h2 r) hmapeq

end S_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero (solution)
