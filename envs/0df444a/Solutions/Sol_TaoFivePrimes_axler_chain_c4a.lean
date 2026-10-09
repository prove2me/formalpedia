-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c4a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:17:57.082889+00:00
-- url     : https://prove2.me/submissions/9ee4e65e-8ac0-4013-a96d-7f2bd532c6f6

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a1
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a2

theorem solution (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) : ((34123262759331 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ≤ (34124678342292 : ℝ)) ∧ (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (34129386 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c4a1 hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c4a2 b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (25762666 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2
