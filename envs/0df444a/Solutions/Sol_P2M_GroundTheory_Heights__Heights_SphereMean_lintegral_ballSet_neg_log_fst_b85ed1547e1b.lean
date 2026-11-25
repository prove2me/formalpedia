-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:30.906794+00:00
-- url     : https://prove2.me/submissions/f219d5bc-bbf9-42e2-bd97-ba625ac089c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_log_pow_84557c7391f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593


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
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log ‖x 0‖) =
      ENNReal.ofReal (π * harmonic (m + 1) / (2 * (m + 1))) * volume (ballSet m 1) := by
  rw [lintegral_ballSet_fst m (fun z => ENNReal.ofReal (-log ‖z‖))
    (ENNReal.measurable_ofReal.comp (measurable_norm.log.neg))]
  congr 1
  have hp : ∀ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ *
      ENNReal.ofReal (-log ‖z‖) =
      ENNReal.ofReal ((Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ < 1
    · simp only [indicator, mem_Iio, hz, ite_true]
      rw [ENNReal.ofReal_mul (by linarith [log_nonpos (norm_nonneg z) hz.le]), mul_comm]
    · simp [indicator, hz]
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_disc_log_pow m), integral_disc_log_pow]
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : ‖z‖ < 1
  · simp only [indicator, mem_Iio, hz, ite_true, Pi.zero_apply]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    exact mul_nonneg (by linarith [log_nonpos (norm_nonneg z) hz.le]) (pow_nonneg (by linarith) m)
  · simp [indicator, hz]
end GroundTheory.Heights₂.Heights.SphereMean
