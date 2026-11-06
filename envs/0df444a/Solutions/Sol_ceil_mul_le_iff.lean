-- Prove2me | solution 1 for ceil_mul_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:50:39.091664+00:00
-- url     : https://prove2.me/submissions/50105f6f-340c-4db3-9691-b41f637918e4

import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit true

variable {n : ℕ} {a x : ℝ}

theorem solution (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [Nat.ceil_le, le_div_iff₀ hx]
