-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_1500_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T16:34:46.265644+00:00
-- url     : https://prove2.me/submissions/8f1fc1a5-8c1a-4d67-9551-cd88afd7fb33

import Theorems.Thm_TaoFivePrimes_primorial_certificate_1499
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_1500_to_2000
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_2000_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser–Schoenfeld product bound (4.10) on the full range 1500 < x ≤ 10^8,
obtained by gluing the finite leg 1500 ≤ x ≤ 2000 (anchored on the exact
primorial certificate at 1499) to the analytic tail 2000 ≤ x ≤ 10^8 at x = 2000. -/
theorem solution (x : ℝ) (hx : 1500 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 2000 with h | h
  · exact rosser_schoenfeld_product_bound_1500_to_2000 x (le_of_lt hx) (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_2000_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 1500 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
