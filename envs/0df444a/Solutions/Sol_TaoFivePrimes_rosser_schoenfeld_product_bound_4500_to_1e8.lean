-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_4500_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T10:44:08.783188+00:00
-- url     : https://prove2.me/submissions/0155518e-aaf9-45a9-abb3-203e88bf61a2

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4500_to_5000
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_5000_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser–Schoenfeld product bound (4.10) on the remaining range 4500 ≤ x ≤ 10^8,
obtained by gluing the finite leg 4500 ≤ x ≤ 5000 (anchored on the exact
primorial certificate at 4493) to the analytic tail 5000 ≤ x ≤ 10^8 at x = 5000. -/
theorem solution (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 5000 with h | h
  · exact rosser_schoenfeld_product_bound_4500_to_5000 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_5000_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
