-- Prove2me | solution 1 for ValueAwareRR.normalizedLossRatio_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:19:07.7718+00:00
-- url     : https://prove2.me/submissions/d7943a2f-5308-4a46-a5cf-1670d1aa60d3

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizedLossRatio_lower_bound

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (N : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ (N : ℚ) ≤ normalizedLossRatio (m : ℚ) := by
  refine ⟨N + 2, by omega, ?_⟩
  have hmQ : (2 : ℚ) ≤ ((N + 2 : ℕ) : ℚ) := by
    exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hb := normalizedLossRatio_lower_bound ((N + 2 : ℕ) : ℚ) hmQ
  have hN : (0 : ℚ) ≤ (N : ℚ) := by positivity
  have hcast : (((N + 2 : ℕ) : ℚ)) = (N : ℚ) + 2 := by norm_num
  calc
    (N : ℚ) ≤ 4 * (((N + 2 : ℕ) : ℚ)) ^ 2 := by
      rw [hcast]
      nlinarith [sq_nonneg ((N : ℚ) + 2)]
    _ ≤ normalizedLossRatio ((N + 2 : ℕ) : ℚ) := hb
end ValueAwareRR
