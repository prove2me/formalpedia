-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_2500_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T17:34:41.787114+00:00
-- url     : https://prove2.me/submissions/2fed8f51-9920-46ee-b36e-059700548ae6

import Theorems.Thm_TaoFivePrimes_primorial_certificate_2477
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_2500_to_3000
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3000_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser-Schoenfeld product bound (4.10) on the full range 2500 <= x <= 10^8,
obtained by gluing the finite leg 2500 <= x <= 3000 (anchored on the exact
primorial certificate at 2477) to the analytic tail 3000 <= x <= 10^8 at x = 3000. -/
theorem solution (x : ℝ) (hx : 2500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 3000 with h | h
  · exact rosser_schoenfeld_product_bound_2500_to_3000 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_3000_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 2500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
