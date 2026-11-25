-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:55.671802+00:00
-- url     : https://prove2.me/submissions/fe49050f-106a-4d57-b6a1-46528e884698

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetBound

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplDetBound
namespace GroundTheory.Heights₂.Heights.PSymplDetBound
theorem _root_.solution (n : ℕ) (ρ : ℝ) (hle : ρ ≤ 2 * ((n : ℝ) + 1)) :
    ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have h0 : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ n := by positivity
  calc ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hle h0
    _ ≤ (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
        push_cast; ring
end GroundTheory.Heights₂.Heights.PSymplDetBound
