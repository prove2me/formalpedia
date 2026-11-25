-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:08.135153+00:00
-- url     : https://prove2.me/submissions/382720af-798c-476f-b1d9-72959e4e0309

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by
  rw [fsLog_pointOf] at hy
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · have := norm_sum_mul_pointOf_le h u y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]; exact this
  rcases (norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha
  · rw [← ha]; positivity
  · have := (Real.log_le_iff_le_exp (div_pos ha h0)).mp hy
    rwa [div_le_iff₀ h0] at this
end GroundTheory.Heights₂.Heights.ConeFsLog
