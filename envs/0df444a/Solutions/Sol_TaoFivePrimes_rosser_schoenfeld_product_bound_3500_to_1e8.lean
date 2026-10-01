-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_3500_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T20:14:49.836841+00:00
-- url     : https://prove2.me/submissions/e0aa8e05-fd34-4224-8ce1-5c0d38aacc48

import Theorems.Thm_TaoFivePrimes_primorial_certificate_3499
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3500_to_4000
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4000_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser-Schoenfeld product bound (4.10) on the full range 3500 <= x <= 10^8,
obtained by gluing the finite leg 3500 <= x <= 4000 (anchored on the exact
primorial certificate at 3499) to the analytic tail 4000 <= x <= 10^8 at x = 4000. -/
theorem solution (x : ℝ) (hx : 3500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 4000 with h | h
  · exact rosser_schoenfeld_product_bound_3500_to_4000 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_4000_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 3500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
