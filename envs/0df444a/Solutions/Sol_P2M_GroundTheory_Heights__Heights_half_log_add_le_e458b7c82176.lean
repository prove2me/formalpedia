-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_half_log_add_le_e458b7c82176
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:21.068886+00:00
-- url     : https://prove2.me/submissions/44b56f14-e3a8-4ef5-b0ac-445643589f09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_log_add_log_two_pi_le_66e18aebe67c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_log_two_pi_le_d42f64adb1d2

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
theorem _root_.solution (D : ℝ) (hD : 1 ≤ D) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D := by
  have h1 := log_add_log_two_pi_le
  have h2 := log_two_pi_le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]
end GroundTheory.Heights₂.Heights
