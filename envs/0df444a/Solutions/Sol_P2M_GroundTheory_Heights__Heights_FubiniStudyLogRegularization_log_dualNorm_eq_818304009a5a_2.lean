-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_log_dualNorm_eq_818304009a5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:02.139388+00:00
-- url     : https://prove2.me/submissions/813d5aeb-2ed9-46c5-8af1-c5e664c84f16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1

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
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
theorem _root_.solution (h : HermNorm n) (y : Fin n → ℂ) :
    Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h 0 1 *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h 0 zero_le_one]
  simp [HermNorm.dualNorm, sqDual]
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
