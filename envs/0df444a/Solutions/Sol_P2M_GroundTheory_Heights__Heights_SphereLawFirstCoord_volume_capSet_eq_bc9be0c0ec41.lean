-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:35.592801+00:00
-- url     : https://prove2.me/submissions/996bd745-25c5-43e4-bac3-49e29cf32b54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c

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
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean
namespace GroundTheory.Heights₂.Heights.SphereLawFirstCoord
theorem _root_.solution {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ENNReal.ofReal ((1 - c) ^ m) * volume (ballSet (m + 1) 1) := by
  have h0 := volume_capSet (m := m) le_rfl zero_lt_one
  have hb : {v : Fin (m + 1) → ℂ | 0 * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ballSet (m + 1) 1 := by
    ext v
    simp [ballSet]
  rw [hb] at h0
  simp only [sub_zero, div_one] at h0
  rw [volume_capSet hc0 hc1, lintegral_scale hc1, mul_assoc, ← h0]
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
