-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:40.380277+00:00
-- url     : https://prove2.me/submissions/92b358ff-4467-43f0-9dc6-d8adb371a9ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_half_log_add_le_e458b7c82176
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd

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
theorem _root_.solution (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ :=
  ⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩
end GroundTheory.Heights₂.Heights
