-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c5a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:30:14.14089+00:00
-- url     : https://prove2.me/submissions/7ff5c34e-4a49-44ba-a993-2f9a6c90776b

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c5a1
import Theorems.Thm_TaoFivePrimes_axler_chain_c5a2

theorem solution (hprev : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) : ((69344896246415 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ≤ (69347654882929 : ℝ)) ∧ (∀ x : ℝ, (52597756 : ℝ) ≤ x → x < (69355435 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c5a1 hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c5a2 b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (60984648 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2
