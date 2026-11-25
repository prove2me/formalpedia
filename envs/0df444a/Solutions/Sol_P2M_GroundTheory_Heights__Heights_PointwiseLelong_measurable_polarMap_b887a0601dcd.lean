-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:41.989857+00:00
-- url     : https://prove2.me/submissions/dd47acda-1a2c-4df1-b7fa-f7522be39633

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4

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
theorem _root_.solution (p : Fin N → ℂ) : Measurable (polarMap p) :=
  (Complex.measurable_arg.comp (continuous_coordAlong p).measurable).prodMk (measurable_radialMap p)
end GroundTheory.Heights₂.Heights.PointwiseLelong
