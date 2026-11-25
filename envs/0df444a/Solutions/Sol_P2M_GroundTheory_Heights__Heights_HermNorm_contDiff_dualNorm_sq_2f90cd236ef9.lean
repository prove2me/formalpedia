-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:31:38.443364+00:00
-- url     : https://prove2.me/submissions/0cc15b2a-f12a-413b-8685-cc6e1c4967c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436

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
    ContDiff ℝ ∞ fun y : Fin n → ℂ => h.dualNorm y ^ 2 := by
  simp_rw [HermNorm.dualNorm_sq]
  refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)
end HermNorm
end GroundTheory.Heights₂.Heights
