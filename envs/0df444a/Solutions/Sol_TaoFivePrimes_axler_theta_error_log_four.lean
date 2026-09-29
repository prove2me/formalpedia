-- Prove2me | solution 1 for TaoFivePrimes.axler_theta_error_log_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-28T14:06:35.683572+00:00
-- url     : https://prove2.me/submissions/17b01ede-6843-4a31-82ae-a4132092fd60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Theorems.Thm_TaoFivePrimes_axler_theta_log_four_finite_certificate
import Theorems.Thm_TaoFivePrimes_axler_theta_log_four_tail

open Finset

theorem solution (x : ℝ) (hx : 70111 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| <
      100 * x / (Real.log x) ^ 4 := by
  by_cases h : x < 10 ^ 8
  · exact TaoFivePrimes.axler_theta_log_four_finite_certificate x hx h
  · exact TaoFivePrimes.axler_theta_log_four_tail x (le_of_not_gt h)
