-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:11.389908+00:00
-- url     : https://prove2.me/submissions/941d3780-8dae-4521-bcc4-3667b973d258

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
namespace HermNorm
theorem _root_.solution (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) {y | y ≠ 0} := by
  have he : (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) =
      fun y => Real.log (h.dualNorm y ^ 2) / 2 := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [he]
  exact (h.contDiff_dualNorm_sq.contDiffOn.log fun y hy =>
    (pow_pos (h.dualNorm_pos hy) 2).ne').div_const 2
end HermNorm
end GroundTheory.Heights₂.Heights
