-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_inner_ball_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-09T23:49:12.755196+00:00
-- url     : https://prove2.me/submissions/ffa4b0f0-4e21-44fb-ac43-2c75eec221af

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_cube
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {δ : ℝ} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (ξ : ℝ) (hδξ : δ * |ξ| ≤ 1)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < δ} m)
    (hsqint : IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < δ} m) :
    ‖∫ x in {x | |x| < δ},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m := by
  have hint : ∫ x in {x | |x| < δ}, (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 ∂m
      = (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m :=
    integral_const_mul _ _
  rw [← hint]
  refine norm_integral_le_of_norm_le (hsqint.const_mul _) ?_
  refine (ae_restrict_iff' ?_).2 (Filter.Eventually.of_forall ?_)
  · exact measurableSet_lt (by fun_prop) measurable_const
  intro x hx
  have hx' : |x| < δ := hx
  have hxξ : |x * ξ| ≤ 1 := by
    rw [abs_mul]
    calc |x| * |ξ| ≤ δ * |ξ| := by gcongr
      _ ≤ 1 := hδξ
  refine (leanlevy_chat31_smallBall_remainder_norm_le_cube hxξ).trans ?_
  have h3 : |x| ^ 3 ≤ δ * x ^ 2 := by
    have : |x| ^ 3 = |x| * x ^ 2 := by
      rw [pow_succ, sq_abs]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx'.le (sq_nonneg x)
  have hc : (0:ℝ) ≤ (2 / 9 : ℝ) * |ξ| ^ 3 := by positivity
  calc (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * (δ * x ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hc
    _ = (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 := by ring
