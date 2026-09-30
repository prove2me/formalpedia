-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_sigma_two_cyclotomic
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T05:45:04.684433+00:00
-- url     : https://prove2.me/submissions/22561483-f67a-4ac0-9ebf-38f2c27c0bc1

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ p : Nat,
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d) := by
  intro h
  have h1 := h 1
  norm_num at h1
