-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:47.062749+00:00
-- url     : https://prove2.me/submissions/590c8c55-4d52-4c9e-96f9-655529e4bc95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1


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
theorem _root_.solution (p : Fin N → ℂ) : Measurable (orthoDir p) := by
  have hc : Continuous fun z => z - coordAlong p z • p :=
    continuous_id.sub ((continuous_coordAlong p).smul continuous_const)
  have hn : Continuous (HermNorm.std N).norm := (HermNorm.std N).li_continuous_norm
  exact ((Complex.measurable_ofReal.comp (hn.comp hc).measurable).inv).smul hc.measurable
end GroundTheory.Heights₂.Heights.PointwiseLelong
