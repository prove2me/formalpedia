-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:29.695567+00:00
-- url     : https://prove2.me/submissions/2866b557-bcbc-4aee-a3ae-a3fc65eddf08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e


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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ) :
    Continuous (coneJacMat h g) := by
  unfold coneJacMat
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (MvPolynomial.continuous_eval _).comp h.continuous_pointOf
end GroundTheory.Heights₂.Heights
