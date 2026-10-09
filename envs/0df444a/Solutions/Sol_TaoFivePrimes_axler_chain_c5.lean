-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:41:31.172287+00:00
-- url     : https://prove2.me/submissions/b5fd25a2-f42a-4abd-b34a-b50036937a97

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c5a
import Theorems.Thm_TaoFivePrimes_axler_chain_c5b
import Theorems.Thm_TaoFivePrimes_axler_chain_c5c

theorem solution (hprev : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) : ((87444803702622 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ≤ (87448235987654 : ℝ)) ∧ (∀ x : ℝ, (52597756 : ℝ) ≤ x → x < (87458565 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c5a hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c5b b1
  obtain ⟨b3, r3⟩ := TaoFivePrimes.axler_chain_c5c b2
  refine ⟨b3, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (69355435 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  rcases lt_or_ge x (77727216 : ℝ) with h2 | h2
  · exact r2 x h1 h2
  exact r3 x h2 hx2
