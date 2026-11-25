-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_log_pow_84557c7391f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:09.726635+00:00
-- url     : https://prove2.me/submissions/0c7a1a3f-8a28-42ab-97c7-15a5c17089fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9

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
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
  apply integrable_disc_radial
  have : (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) =
      fun y => -(y * log y) * (1 - y ^ 2) ^ m := by
    funext y; ring
  rw [this]
  exact (continuous_mul_log.neg.mul (by fun_prop)).continuousOn
end GroundTheory.Heights₂.Heights.SphereMean
