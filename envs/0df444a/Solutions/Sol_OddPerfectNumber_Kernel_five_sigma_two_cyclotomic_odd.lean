-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T05:45:31.489632+00:00
-- url     : https://prove2.me/submissions/10678ac9-c8ec-433b-8925-29a07228268f

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ (p : Nat), Odd p →
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d) := by
  intro h
  have h1 := h 1 (by decide)
  norm_num at h1
