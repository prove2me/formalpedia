-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_log_two_pi_le_d42f64adb1d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:54.354006+00:00
-- url     : https://prove2.me/submissions/6b764300-1db6-4e62-bcd8-d3587620bafb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_log_add_log_two_pi_le_66e18aebe67c

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
open Real
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith
end GroundTheory.Heights₂.Heights
