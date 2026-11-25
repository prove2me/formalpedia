-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:32.66052+00:00
-- url     : https://prove2.me/submissions/63056b83-4757-458c-bcdd-f91260ae1243

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable

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
theorem _root_.solution (m : ℕ) : Continuous (gramOp (n := n) (m := m)) := by
  have hL : Continuous fun π : Fin m → Fin n → ℂ =>
      LinearMap.toContinuousLinearMap (linProjₗ π) := by
    refine continuous_clm_apply.2 fun v => ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    change Continuous fun π : Fin m → Fin n → ℂ => linProj π v
    unfold linProj
    fun_prop
  exact (ContinuousLinearMap.adjoint.continuous.comp hL).clm_comp hL
end GroundTheory.Heights₂.Heights
