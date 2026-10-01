-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_3000_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T17:46:04.304197+00:00
-- url     : https://prove2.me/submissions/2d912e4f-cb73-4b8e-9075-6df0ce124ac0

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3000_to_3500
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3500_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser-Schoenfeld product bound (4.10) on the full range 3000 <= x <= 10^8,
obtained by gluing the finite leg 3000 <= x <= 3500 (anchored on the exact
primorial certificate at 2999) to the analytic tail 3500 <= x <= 10^8 at x = 3500. -/
theorem solution (x : ℝ) (hx : 3000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 3500 with h | h
  · exact rosser_schoenfeld_product_bound_3000_to_3500 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_3500_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 3000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
