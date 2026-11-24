-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:52.555426+00:00
-- url     : https://prove2.me/submissions/79c6a095-e177-4fc9-a955-d8fbf5996815

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
theorem _root_.solution (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex]
  have h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) =
      (Iio (1 : ℝ)).indicator (fun y => y * g y) := by
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact (hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self
end GroundTheory.Heights₂.Heights.SphereMean
