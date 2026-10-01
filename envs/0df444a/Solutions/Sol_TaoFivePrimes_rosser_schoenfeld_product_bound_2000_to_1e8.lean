-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_2000_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T16:51:26.749713+00:00
-- url     : https://prove2.me/submissions/ec498c83-d7f8-478c-995d-83708a6b9d59

import Theorems.Thm_TaoFivePrimes_primorial_certificate_1999
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_2000_to_2500
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_2500_to_1e8
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser–Schoenfeld product bound (4.10) on the full range 2000 ≤ x ≤ 10^8,
obtained by gluing the finite leg 2000 ≤ x ≤ 2500 (anchored on the exact
primorial certificate at 1999) to the analytic tail 2500 ≤ x ≤ 10^8 at x = 2500. -/
theorem solution (x : ℝ) (hx : 2000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 2500 with h | h
  · exact rosser_schoenfeld_product_bound_2000_to_2500 x hx (le_of_lt h)
  · exact rosser_schoenfeld_product_bound_2500_to_1e8 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 2000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
