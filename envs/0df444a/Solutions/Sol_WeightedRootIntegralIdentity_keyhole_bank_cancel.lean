-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_bank_cancel
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:48:05.008684+00:00
-- url     : https://prove2.me/submissions/58fad6c6-d639-47c0-837f-5e464490c9a2

import Mathlib
open scoped Interval

theorem solution {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in a..b, f x) + (∫ x in b..a, f x) = 0 := by
  rw [intervalIntegral.integral_symm]
  ring
