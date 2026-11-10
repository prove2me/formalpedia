-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_crude
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:51:29.16849+00:00
-- url     : https://prove2.me/submissions/26d94695-1ead-4b40-99c4-69e1be4f2e9f

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The original uniform unit-ball estimate used for integrability after clamping. -/
theorem solution
    {ξ x : ℝ} (hx : |x| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
      + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by
  have harg : (↑x : ℂ) * ↑ξ * I = (↑(x * ξ) : ℂ) * I := by push_cast; ring
  have hexp_norm : ‖exp ((↑x : ℂ) * ↑ξ * I)‖ = 1 := by
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hxξ : ‖(↑x : ℂ) * ↑ξ * I‖ = |x| * |ξ| := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have hsq : ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ = (|x| * |ξ|) ^ 2 / 2 := by
    rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  calc
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
        + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖
      ≤ ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I‖
          + ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ := norm_add_le _ _
    _ ≤ (‖exp ((↑x : ℂ) * ↑ξ * I) - 1‖ + ‖(↑x : ℂ) * ↑ξ * I‖)
          + ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ ((‖exp ((↑x : ℂ) * ↑ξ * I)‖ + ‖(1 : ℂ)‖)
          + ‖(↑x : ℂ) * ↑ξ * I‖) + ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ := by
          gcongr
          exact norm_sub_le _ _
    _ = 2 + |x| * |ξ| + (|x| * |ξ|) ^ 2 / 2 := by
          rw [hexp_norm, hxξ, hsq, norm_one]
          ring
    _ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by
          have hxξ_le : |x| * |ξ| ≤ |ξ| := by
            calc
              |x| * |ξ| ≤ 1 * |ξ| := by gcongr
              _ = |ξ| := one_mul _
          have hsq_le : (|x| * |ξ|) ^ 2 / 2 ≤ ξ ^ 2 / 2 := by
            have hnn : (0 : ℝ) ≤ |x| * |ξ| := by positivity
            have : (|x| * |ξ|) ^ 2 ≤ |ξ| ^ 2 := by gcongr
            rw [sq_abs] at this
            linarith
          linarith
