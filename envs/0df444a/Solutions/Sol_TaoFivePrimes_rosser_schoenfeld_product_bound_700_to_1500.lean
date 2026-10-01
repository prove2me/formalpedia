-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_700_to_1500
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T16:22:04.735655+00:00
-- url     : https://prove2.me/submissions/a9955a73-cc67-4221-9174-0af06fb88bfa

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_700_to_1050
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_1050_to_1500
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

/-- The Rosser–Schoenfeld product bound (4.10) on the full range 700 ≤ x ≤ 1500,
obtained by gluing the two adjacent finite-range legs at x = 1050. -/
theorem solution (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 1500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 1050 with h | h
  · exact rosser_schoenfeld_product_bound_700_to_1050 x hx h
  · exact rosser_schoenfeld_product_bound_1050_to_1500 x h hx'

end TaoFivePrimes

theorem solution (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 1500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
