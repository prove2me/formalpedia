-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_31_length_multiple_five_implies_eleven
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:17:08.580529+00:00
-- url     : https://prove2.me/submissions/bd05a7eb-b6ea-4080-8285-ea43ae3b9b64

import Mathlib

theorem solution (e : Nat) (h : 5 ∣ 2 * e + 1) :
    11 ∣ ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  have blocks : ∀ k : ℕ, 11 ∣ ∑ i ∈ Finset.range (5 * k), 31 ^ i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      apply dvd_add ih
      simp_rw [pow_add]
      rw [← Finset.mul_sum]
      apply dvd_mul_of_dvd_right
      norm_num [Finset.sum_range_succ]
  exact blocks k

#print axioms solution
