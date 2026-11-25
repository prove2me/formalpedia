-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:58.662412+00:00
-- url     : https://prove2.me/submissions/364ec633-847f-4a80-99ab-c72afbca9eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_seven_point_six_le_log_8b8879536309

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
theorem _root_.solution (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by
  have h := seven_point_six_le_log ρ hρ
  nlinarith [mul_le_mul_of_nonneg_left h hD]
end GroundTheory.Heights₂.Heights
