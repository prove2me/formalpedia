-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:13:23.806891+00:00
-- url     : https://prove2.me/submissions/d82bc947-b970-433e-9f95-6afc126aeb7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (hF : Differentiable ℂ F)
    (z : EuclideanSpace ℂ (Fin N)) :
    ‖F 0‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
  set h : ℂ → ℂ := fun w => F (w • z) ^ 2 with hh
  have hd : Differentiable ℂ h := by
    first
      | exact (hF.comp (differentiable_id.smul_const z)).pow 2
      | (rw [hh]; fun_prop)
  have hc := (hd.diffContOnCl (s := Metric.ball (0 : ℂ) 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul
    (Metric.mem_ball_self one_pos)
  have hI : (∮ w in C(0, 1), (w - 0)⁻¹ • h w)
      = Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ) := by
    first | rw [circleIntegral] | unfold circleIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hc0 : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    simp only [deriv_circleMap, smul_eq_mul, sub_zero]
    rw [mul_comm (circleMap 0 1 θ) Complex.I, mul_assoc, mul_inv_cancel_left₀ hc0]
  rw [hI, smul_eq_mul] at hc
  have h0 : ‖F 0‖ ^ 2 = ‖h 0‖ := by simp [hh, norm_pow]
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖Complex.I‖ = (2 * Real.pi)⁻¹ := by
    first
      | simp [abs_of_pos Real.pi_pos]
      | (simp [abs_of_pos Real.pi_pos]; ring)
      | (simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos])
  have hle : ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖
      ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
    simp [hh, norm_pow]
  rw [h0, ← hc, norm_mul, norm_mul]
  calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (‖Complex.I‖ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖)
      = (‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖Complex.I‖)
          * ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖ := by ring
    _ ≤ _ := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
end ReciprocityTheory.ChartRestriction.G.I2
