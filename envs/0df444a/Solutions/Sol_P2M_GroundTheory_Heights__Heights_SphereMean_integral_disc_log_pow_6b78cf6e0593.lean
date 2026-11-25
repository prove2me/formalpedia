-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:22.315811+00:00
-- url     : https://prove2.me/submissions/9be1dac7-87d5-4566-83fa-9c322601819e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_radial_a4bc8781ded8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_weight_639b4831e09d


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
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by
  rw [integral_disc_radial]
  have h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) =
      -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [h, integral_disc_log_weight]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.SphereMean
