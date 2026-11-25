-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:34.39586+00:00
-- url     : https://prove2.me/submissions/5bddb16d-d26b-4358-824d-a9f2576f8d4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_pow_837dc17a5adc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) :
    volume (ballSet (m + 1) 1) = ENNReal.ofReal (π / (m + 1)) * volume (ballSet m 1) := by
  have h := lintegral_ballSet_fst m (fun _ => 1) measurable_const
  simp only [setLIntegral_one, mul_one] at h
  rw [h]
  congr 1
  have hp : ∀ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ =
      ENNReal.ofReal ((Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ < 1 <;> simp [indicator, hz]
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_disc_pow m), integral_disc_pow]
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : ‖z‖ < 1
  · simp only [indicator, mem_Iio, hz, ite_true, Pi.zero_apply]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    exact pow_nonneg (by linarith) m
  · simp [indicator, hz]
end GroundTheory.Heights₂.Heights.SphereMean
