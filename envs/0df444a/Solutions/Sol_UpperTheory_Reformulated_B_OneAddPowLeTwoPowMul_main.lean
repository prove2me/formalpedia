-- Prove2me | solution 1 for UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:36.467017+00:00
-- url     : https://prove2.me/submissions/360f9c7c-3978-4a81-aefe-9406df8c7770

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FirstStatementC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul
theorem _root_.solution :
    ∀ (t : ℝ), (0 : ℝ) ≤ t → ∀ (N : ℕ), ((1 : ℝ) + t) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + t ^ N) := by
  intro t ht N
  have h1 : (1 : ℝ) + t ≤ 2 * max 1 t := by
    linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
  have h2 : ((1 : ℝ) + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow] at h2
  have h3 : (max (1 : ℝ) t) ^ N ≤ 1 + t ^ N := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
      linarith
    · rw [max_eq_right h]
      linarith
  calc ((1 : ℝ) + t) ^ N ≤ 2 ^ N * (max 1 t) ^ N := h2
    _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left h3 (by positivity)
end UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul
