-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:42.779633+00:00
-- url     : https://prove2.me/submissions/d11c836d-b0a2-4c66-9837-9e44691658dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : r ^ (2 * m - 1) ≤ (1 + r ^ 2) ^ m := by
  rcases le_total r 1 with h | h
  · exact (pow_le_one₀ hr h).trans (one_le_pow₀ (by nlinarith))
  · calc r ^ (2 * m - 1) ≤ r ^ (2 * m) := pow_le_pow_right₀ h (Nat.sub_le _ _)
      _ = (r ^ 2) ^ m := by rw [pow_mul]
      _ ≤ (1 + r ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg r) (by linarith) m
end GroundTheory.Heights₂.Heights
