-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_prime
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T05:52:40.504982+00:00
-- url     : https://prove2.me/submissions/a7a3641c-62b0-4942-b697-dacf5082c042

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ (p : Nat), p.Prime →
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d) := by
  intro h
  have h2 := h 2 Nat.prime_two
  rw [Nat.sum_divisors_prime_pow Nat.prime_two] at h2
  norm_num [Finset.sum_range_succ] at h2
