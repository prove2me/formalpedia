-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_5000_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T23:09:28.96+00:00
-- url     : https://prove2.me/submissions/f9fa9459-77b3-4a7b-ad07-a16cb2d5cd0f

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4500_to_1e8
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 5000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  exact TaoFivePrimes.rosser_schoenfeld_product_bound_4500_to_1e8 x (by linarith) hx'

#print axioms solution
