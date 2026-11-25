-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:58.082832+00:00
-- url     : https://prove2.me/submissions/4e4a2b82-f4d5-41c7-a113-e824b1dcdffa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall
namespace GroundTheory.Heights₂.Heights.SphereMeanLinearBall
theorem _root_.solution (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
end GroundTheory.Heights₂.Heights.SphereMeanLinearBall
