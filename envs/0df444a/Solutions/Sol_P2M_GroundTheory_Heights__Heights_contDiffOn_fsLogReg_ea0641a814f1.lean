-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:18.851022+00:00
-- url     : https://prove2.me/submissions/434f3130-a192-4199-9c83-0b04b156ed85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {y | y ≠ 0} := by
  have hnum : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2 :=
    ((contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))).add
      (contDiff_const.mul h.contDiff_dualNorm_sq)
  have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < h.dualNorm y ^ 2 := fun y hy =>
    pow_pos (h.dualNorm_pos hy) 2
  refine ((hnum.contDiffOn.div h.contDiff_dualNorm_sq.contDiffOn fun y hy => (hpos y hy).ne').log
    fun y hy => ?_).div_const 2
  have := hpos y hy
  exact (div_pos (by positivity) this).ne'
end GroundTheory.Heights₂.Heights
