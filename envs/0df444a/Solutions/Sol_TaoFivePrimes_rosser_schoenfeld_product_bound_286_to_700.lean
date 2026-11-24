-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_286_to_700
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T04:28:19.456267+00:00
-- url     : https://prove2.me/submissions/704faa36-07c4-452f-aad0-f7865bf5d3eb

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_finite

theorem solution (x : ℝ) (hx : 286 ≤ x) (hx' : x < 700) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x * (1 + 1 / (2 * (Real.log x) ^ 2)) :=
  TaoFivePrimes.rosser_schoenfeld_product_bound_finite x hx hx'

#check @solution
