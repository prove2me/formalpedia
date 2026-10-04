-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_index_dvd_three_of_euler
-- status  : ACCEPTED   (disprove)
-- author  : @os0xcom
-- created : 2026-10-03T15:45:35.574219+00:00
-- url     : https://prove2.me/submissions/399e38df-9caf-4f03-99b6-b14867d802b7

import Mathlib

set_option linter.unusedVariables false

theorem solution :
    ¬ (∀ (p m s : Nat) (_hp : p.Prime) (_hp2 : p != 2) (_hs : s != 0)
        (_h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s), 3 ∣ s) := by
  intro h
  have hprime : Nat.Prime 5 := by decide
  have hsum : (∑ d ∈ (5 ^ 5).divisors, d) = ∑ i ∈ Finset.range 6, 5 ^ i := by
    rw [Nat.divisors_prime_pow hprime 5, Finset.sum_map]
    rfl
  have hclosed : (∑ i ∈ Finset.range 6, 5 ^ i) = 3906 := by
    repeat rw [Finset.sum_range_succ]
    norm_num
  have heq : 2 * 651 ^ 2 = (∑ d ∈ (5 ^ 5).divisors, d) * 217 := by
    rw [hsum, hclosed]
    norm_num
  have hnot : ¬ 3 ∣ 217 := by decide
  exact hnot (h 5 651 217 (by decide) (by decide) (by decide) heq)
