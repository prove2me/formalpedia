-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_4000_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T20:43:10.109812+00:00
-- url     : https://prove2.me/submissions/71209b60-a638-4ae1-8679-ca588c7b4c80

import Theorems.Thm_TaoFivePrimes_primorial_certificate_3989
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4000_to_4500
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4500_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser-Schoenfeld product bound (4.10) on the remaining range 4000 <= x <= 10^8,
obtained by gluing the finite leg 4000 <= x <= 4500 (anchored on the exact
primorial certificate at 3989) to the analytic tail 4500 <= x <= 10^8 at x = 4500. -/
theorem solution (x : ℝ) (hx : 4000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 4500 with h | h
  · exact rosser_schoenfeld_product_bound_4000_to_4500 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_4500_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 4000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
