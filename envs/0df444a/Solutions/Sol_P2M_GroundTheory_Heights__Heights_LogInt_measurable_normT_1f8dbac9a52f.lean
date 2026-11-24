-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:59.790591+00:00
-- url     : https://prove2.me/submissions/c27fc96a-56ea-4f87-8d68-e0d95d000125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (T : Finset (Fin k)) : Measurable (normT h T) := by
  refine measurable_pi_lambda _ fun ij => ?_
  by_cases hT : ij.1 ∈ T
  · simp only [normT, hT, if_true]
    exact (Complex.measurable_ofReal.comp (measurable_groupNorm h ij.1)).inv.mul
      (measurable_pi_apply _)
  · simp only [normT, hT, if_false]
    exact measurable_pi_apply _
end GroundTheory.Heights₂.Heights.LogInt
