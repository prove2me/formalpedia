-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:21.166667+00:00
-- url     : https://prove2.me/submissions/8e3b45c5-cb0f-40d6-83ca-c46155811f5e

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
theorem _root_.solution (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y v : EuclideanSpace ℂ (Fin n)) :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) ↔
      ∀ i, ∑ j, eval (h.pointOf y) (pderiv j (g i)) * h.pointOf v j = 0 := by
  rw [LinearMap.mem_ker]
  change WithLp.toLp 2 (Matrix.mulVec (coneJacMat h g y) (WithLp.ofLp v)) = 0 ↔ _
  rw [WithLp.toLp_eq_zero, coneJacMat, ← Matrix.mulVec_mulVec, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rfl
end GroundTheory.Heights₂.Heights
