-- Prove2me | solution 1 for TaoFivePrimes.axler_chain_c4b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:24:02.40547+00:00
-- url     : https://prove2.me/submissions/eea7dee3-d618-4536-8e34-7e21b948a00b

import Mathlib
import Theorems.Thm_TaoFivePrimes_axler_chain_c4b1
import Theorems.Thm_TaoFivePrimes_axler_chain_c4b2

theorem solution (hprev : (34123262759331 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ≤ (34124678342292 : ℝ)) : ((52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) ∧ (∀ x : ℝ, (34129386 : ℝ) ≤ x → x < (52597756 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c4b1 hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c4b2 b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (42496200 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2
