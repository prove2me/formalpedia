-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:48.945444+00:00
-- url     : https://prove2.me/submissions/f1a1bd5f-6b1b-4c8c-b3d4-4be726a839fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9


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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {t : ℂ} (ht : t ≠ 0)
    (y : Fin n → ℂ) : fsLogReg h u ε (t • y) = fsLogReg h u ε y := by
  have hu : ‖∑ j, u j * (t • y) j‖ = ‖t‖ * ‖∑ j, u j * y j‖ := by
    rw [← norm_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hu, h.dualNorm_smul, mul_pow, mul_pow, ← mul_assoc, mul_comm ε, mul_assoc, ← mul_add,
    mul_div_mul_left _ _ ht2]
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
