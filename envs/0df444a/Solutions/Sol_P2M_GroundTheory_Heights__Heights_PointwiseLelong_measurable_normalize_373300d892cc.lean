-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:20.331993+00:00
-- url     : https://prove2.me/submissions/b2578e96-210f-41cd-991c-7d862ba173f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90


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
theorem _root_.solution :
    Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) => sphereNormalize (HermNorm.std N) 1 u (0, j) := by
  refine measurable_pi_lambda _ fun j => ?_
  exact ((Complex.measurable_ofReal.comp (LogInt.measurable_groupNorm _ 0)).inv).mul
    (measurable_pi_apply _)
end GroundTheory.Heights₂.Heights.PointwiseLelong
