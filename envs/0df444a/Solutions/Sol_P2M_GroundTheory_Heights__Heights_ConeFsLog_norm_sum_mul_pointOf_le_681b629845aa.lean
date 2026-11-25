-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:42.189799+00:00
-- url     : https://prove2.me/submissions/0fe77fec-8711-45ef-b94c-f3678ece8397

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49

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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeFsLog
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by
  rw [sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
end GroundTheory.Heights₂.Heights.ConeFsLog
