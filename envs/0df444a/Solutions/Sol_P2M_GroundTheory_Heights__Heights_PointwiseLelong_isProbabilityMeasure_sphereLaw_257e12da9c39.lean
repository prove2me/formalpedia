-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_isProbabilityMeasure_sphereLaw_257e12da9c39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:31:59.910264+00:00
-- url     : https://prove2.me/submissions/35e33409-d1b7-4f59-9fe6-98b908a79026

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6

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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution : IsProbabilityMeasure (sphereLaw N) := by
  have := cond_isProbabilityMeasure_of_finite (volume_sphereBall_ne_zero (N := N))
    volume_sphereBall_ne_top
  exact Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable
end GroundTheory.Heights₂.Heights.PointwiseLelong
