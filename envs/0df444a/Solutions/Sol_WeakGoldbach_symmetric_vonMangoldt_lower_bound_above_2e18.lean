-- Prove2me | solution 1 for WeakGoldbach.symmetric_vonMangoldt_lower_bound_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T03:02:56.893554+00:00
-- url     : https://prove2.me/submissions/029171bf-53fd-4a33-9912-74d4831c95e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_weighted_symmetric_main_term_above_2e18

theorem _root_.solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (5 / 4 : ℝ) *
      (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      (m : ℝ) ≤
    ∑ t ∈ Finset.range (m - 1),
      ArithmeticFunction.vonMangoldt (m - t) * ArithmeticFunction.vonMangoldt (m + t) := by
  have h := WeakGoldbach.weighted_symmetric_main_term_above_2e18 m hm
  linarith [h]

#print axioms solution
