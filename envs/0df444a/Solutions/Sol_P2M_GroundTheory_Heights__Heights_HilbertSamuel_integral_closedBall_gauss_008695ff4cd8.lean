-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_integral_closedBall_gauss_008695ff4cd8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:12.480082+00:00
-- url     : https://prove2.me/submissions/3c62e1c8-9e0f-4275-bae2-e2ad8d5c8016

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (c ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) =
      if c = 0 then π * ρ ^ 2 else π * (1 - Real.exp (-c * ρ ^ 2)) / c := by
  have h0 : ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) =
      ∫ z : ℂ, (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) ‖z‖ := by
    rw [← integral_indicator measurableSet_closedBall]
    congr 1
    funext z
    by_cases hz : ‖z‖ ≤ ρ <;> simp [indicator, hz]
  rw [h0, integral_fun_norm_addHaar volume (fun r => (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y =
      ∫ y in (0 : ℝ)..ρ, y * Real.exp (-c * y ^ 2) := by
    have : (fun y : ℝ => y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y) =
        (Iic ρ).indicator (fun y => y * Real.exp (-c * y ^ 2)) := by
      funext y
      by_cases hy : y ≤ ρ <;> simp [indicator, hy]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
      intervalIntegral.integral_of_le hρ]
  rw [h1]
  by_cases hc : c = 0
  · subst hc
    simp only [if_true]
    have : ∫ y in (0 : ℝ)..ρ, y * Real.exp (-0 * y ^ 2) = ρ ^ 2 / 2 := by
      simp
    rw [this]
    simp [nsmul_eq_mul]
    ring
  · simp only [hc, if_false]
    have hd : ∀ y ∈ uIcc 0 ρ, HasDerivAt (fun y : ℝ => -Real.exp (-c * y ^ 2) / (2 * c))
        (y * Real.exp (-c * y ^ 2)) y := by
      intro y _
      have := (((hasDerivAt_pow 2 y).const_mul (-c)).exp.neg).div_const (2 * c)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp [nsmul_eq_mul]
    field_simp
    ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
