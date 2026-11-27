-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:34.325912+00:00
-- url     : https://prove2.me/submissions/04a32fe1-b774-4a3b-9f8e-05bc90391632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_sqDual_73944ddad90b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {x | x ≠ 0} := by
  intro y hy
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  have hD : ContDiffAt ℝ ∞ (fun y => (‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) y :=
    (((contDiff_lin u).add (contDiff_const.mul (contDiff_sqDual h))).contDiffAt).div
      (contDiff_sqDual h).contDiffAt hS.ne'
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((hD.log (div_pos hN hS).ne').div_const 2).contDiffWithinAt
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
