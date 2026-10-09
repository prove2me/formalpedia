-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:35:48.707338+00:00
-- url     : https://prove2.me/submissions/70ce63ba-58ef-45cf-a073-c5b791625cf8

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a
import Theorems.Thm_TaoFivePrimes_axler_chain_c4b

theorem solution (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) : ((52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) ∧ (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (52597756 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c4a hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c4b b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (34129386 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2
