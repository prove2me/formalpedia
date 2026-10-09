-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:13:36.404883+00:00
-- url     : https://prove2.me/submissions/73e18743-007f-45d6-aeaf-003343ab1e1e

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c3a
import Theorems.Thm_TaoFivePrimes_axler_chain_c3b

theorem solution (hprev : (1697867131810 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ≤ (1697951293771 : ℝ)) : ((17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) ∧ (∀ x : ℝ, (1699362 : ℝ) ≤ x → x < (17387265 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c3a hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c3b b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (8409485 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2
