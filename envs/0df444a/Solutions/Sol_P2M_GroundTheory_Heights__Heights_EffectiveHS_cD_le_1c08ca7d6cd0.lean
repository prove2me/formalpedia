-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:02.794484+00:00
-- url     : https://prove2.me/submissions/2e88c7c5-6c95-414a-8b22-e895dfff66bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution (D : ℕ) : cD D ≤ 2 * (2 * Real.pi) ^ D := by
  unfold cD
  have h1 : (1 : ℝ) ≤ (D - 1).factorial := by exact_mod_cast Nat.factorial_pos (D - 1)
  have h0 : (0 : ℝ) ≤ 2 ^ (D + 1) * Real.pi ^ D := by have := Real.pi_pos; positivity
  calc 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial ≤ 2 ^ (D + 1) * Real.pi ^ D :=
        div_le_self h0 h1
    _ = 2 * (2 * Real.pi) ^ D := by rw [mul_pow, pow_succ]; ring
end GroundTheory.Heights₂.Heights.EffectiveHS
