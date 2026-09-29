-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_local_strength
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T04:43:00.873056+00:00
-- url     : https://prove2.me/submissions/1b0d5761-24e4-4e76-9993-e06f1d7f5794

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap Matrix

namespace USGAux

lemma opNorm_le_one {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ x : n → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2) : opNorm A ≤ 1 := by
  unfold opNorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Matrix.ofLp_toEuclideanCLM]
  exact h x.ofLp

end USGAux

open USGAux in
theorem solution
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    localInteractionStrength ((a : ℂ) • switchProjector)
      (switchGuard + (b : ℂ) • switchExchange) switchGuard ≤ 1 := by
  have ha1 : |a| ≤ 1 := by linarith
  have h1 : opNorm ((a : ℂ) • switchProjector) ≤ 1 := by
    apply opNorm_le_one
    intro x
    simp [Fin.sum_univ_three, Matrix.mulVec, dotProduct, switchProjector, norm_mul]
    have hx1 := norm_nonneg (x 1)
    have hx2 := norm_nonneg (x 2)
    have hx0 := norm_nonneg (x 0)
    have : |a| ^ 2 ≤ 1 := by nlinarith [abs_nonneg a]
    nlinarith [sq_nonneg ‖x 1‖, sq_nonneg ‖x 2‖, sq_nonneg ‖x 0‖, mul_le_mul_of_nonneg_right this (sq_nonneg ‖x 1‖),
      mul_le_mul_of_nonneg_right this (sq_nonneg ‖x 2‖)]
  have h3 : opNorm switchGuard ≤ 1 := by
    apply opNorm_le_one
    intro x
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.mulVec, dotProduct, switchGuard]
    nlinarith [sq_nonneg ‖x (0, 0)‖, sq_nonneg ‖x (1, 1)‖, sq_nonneg ‖x (1, 2)‖,
      sq_nonneg ‖x (2, 1)‖, sq_nonneg ‖x (2, 2)‖]
  have h2 : opNorm (switchGuard + (b : ℂ) • switchExchange) ≤ 1 := by
    apply opNorm_le_one
    intro x
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.mulVec, dotProduct, switchGuard,
      switchExchange, switchVector, norm_mul]
    have hsub : ‖x (1, 2) - x (2, 1)‖ ^ 2 ≤ 2 * (‖x (1, 2)‖ ^ 2 + ‖x (2, 1)‖ ^ 2) := by
      have := norm_sub_le (x (1, 2)) (x (2, 1))
      nlinarith [norm_nonneg (x (1, 2)), norm_nonneg (x (2, 1)), norm_nonneg (x (1, 2) - x (2, 1)),
        sq_nonneg (‖x (1, 2)‖ - ‖x (2, 1)‖)]
    have hb2 : |b| ^ 2 ≤ 1 / 4 := by
      rw [abs_of_pos hb]; nlinarith
    have e1 : ‖(b : ℂ) * x (1, 2) + -((b : ℂ) * x (2, 1))‖ = |b| * ‖x (1, 2) - x (2, 1)‖ := by
      rw [← sub_eq_add_neg, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖-((b : ℂ) * x (1, 2)) + (b : ℂ) * x (2, 1)‖ = |b| * ‖x (1, 2) - x (2, 1)‖ := by
      rw [neg_add_eq_sub, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    rw [e1, e2, mul_pow]
    nlinarith [sq_nonneg ‖x (0, 0)‖, sq_nonneg ‖x (1, 1)‖, sq_nonneg ‖x (2, 2)‖,
      sq_nonneg ‖x (1, 2)‖, sq_nonneg ‖x (2, 1)‖, mul_le_mul_of_nonneg_right hb2
        (sq_nonneg ‖x (1, 2) - x (2, 1)‖), sq_nonneg (|b|)]
  unfold localInteractionStrength
  exact max_le h1 (max_le h2 h3)
