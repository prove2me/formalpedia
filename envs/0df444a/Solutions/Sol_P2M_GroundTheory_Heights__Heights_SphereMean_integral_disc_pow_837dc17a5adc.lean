-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_pow_837dc17a5adc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:21.40865+00:00
-- url     : https://prove2.me/submissions/b1235b7e-6168-49d5-a69d-1549157b05e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_radial_a4bc8781ded8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4


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
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖ = π / (m + 1) := by
  rw [integral_disc_radial, integral_disc_weight]
  field_simp
end GroundTheory.Heights₂.Heights.SphereMean
