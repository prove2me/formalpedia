-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:54:26.104601+00:00
-- url     : https://prove2.me/submissions/24bf8d21-1876-4cbb-b423-189ed7ee22d5

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (p : Nat) (hp : p.Prime) (hp2 : p != 2) :
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d := by
  have hp2' : p ≠ 2 := by simpa using hp2
  have hodd := hp.odd_of_ne_two hp2'
  obtain ⟨k, hk⟩ := hodd
  have hm : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hle : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  calc
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
        (2 * ((p + 1) / 2)) * (p ^ 2 + p + 1) * (p ^ 2 - p + 1) := by ring
    _ = (p + 1) * (p ^ 2 + p + 1) * (p ^ 2 - p + 1) := by rw [hm]
    _ = ∑ d ∈ (p ^ 5).divisors, d := by
      rw [Nat.sum_divisors_prime_pow hp]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      zify [hle]
      ring
