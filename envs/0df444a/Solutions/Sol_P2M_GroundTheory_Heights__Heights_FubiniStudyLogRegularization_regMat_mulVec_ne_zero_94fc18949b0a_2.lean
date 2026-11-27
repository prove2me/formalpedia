-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_regMat_mulVec_ne_zero_94fc18949b0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:58.114718+00:00
-- url     : https://prove2.me/submissions/e446ff4e-d0be-4164-a74c-fb9447883c0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sqDual_pos_386ce14d2e20
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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℂ}
    (hy : y ≠ 0) : regMat h u ε *ᵥ y ≠ 0 := by
  intro h0
  have hs := sum_regMat h u hε.le y
  rw [h0] at hs
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hs
  nlinarith
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
