-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:45.999983+00:00
-- url     : https://prove2.me/submissions/103fc642-431c-4a24-b089-4d2d5fd40dbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) :
    fsLogReg h u ε y = Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 := by
  rw [fsLogReg, dualNorm_sq]
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
