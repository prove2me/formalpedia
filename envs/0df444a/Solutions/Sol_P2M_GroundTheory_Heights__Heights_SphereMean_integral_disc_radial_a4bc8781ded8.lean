-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_radial_a4bc8781ded8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.012992+00:00
-- url     : https://prove2.me/submissions/94fa4874-64bf-4a9b-88f0-4da9c9cdf939

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc

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
theorem _root_.solution (g : ℝ → ℝ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator g ‖z‖ = 2 * π * ∫ y in (0 : ℝ)..1, y * g y := by
  rw [integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y =
      ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y := by
    congr 1
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [nsmul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.SphereMean
