-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_add_log_0720d50c2495
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:39.93588+00:00
-- url     : https://prove2.me/submissions/32360997-5105-4ce0-8c20-08f908f3ecd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℂ) :
    fsLogReg h u ε y + Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h u hε.le, fsLogReg_eq]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [HermNorm.dualNorm, sqDual]
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  rw [Real.log_div hN.ne' hS.ne', Real.log_sqrt hN.le, HermNorm.dualNorm,
    show ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 = sqDual h y from rfl, Real.log_sqrt hS.le]
  ring
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
