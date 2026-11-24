-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:24.725678+00:00
-- url     : https://prove2.me/submissions/ececbd65-64de-4439-815e-860998bc1283

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_dualNorm_sq_dbc05d1fc4c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb


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
theorem _root_.solution (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < sqDual h y := by
  rw [← dualNorm_sq]
  exact pow_pos (h.dualNorm_pos hy) 2
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
