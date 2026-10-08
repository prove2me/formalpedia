-- Prove2me | solution 1 for OddPerfectNumber.Kernel.p5_q31_local_factor_forces_d1_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T07:36:40.989672+00:00
-- url     : https://prove2.me/submissions/db1d131b-4697-48c3-abe4-db8bcaf21441

import Mathlib

theorem solution (m d1 : Nat)
    (hm : m = 651 * d1)
    (hsupp : ∀ l : Nat, l.Prime →
      l ∣ (∑ i ∈ Finset.range (2 * 2 + 1), 31 ^ i) →
      l = 5 ∨ l = 31 ∨ l = 7 ∨ l ∣ m) :
    11 ∣ d1 ∧ 17351 ∣ d1 := by
  have hsum : (∑ i ∈ Finset.range (2 * 2 + 1), 31 ^ i) = 5 * 11 * 17351 := by
    norm_num [Finset.sum_range_succ]
  have h11m : 11 ∣ m := by
    have h := hsupp 11 (by norm_num) (by rw [hsum]; norm_num)
    rcases h with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h
  have h17351m : 17351 ∣ m := by
    have h := hsupp 17351 (by norm_num) (by rw [hsum]; norm_num)
    rcases h with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h
  rw [hm] at h11m h17351m
  have h11 : 11 ∣ d1 := by
    rcases ((by norm_num : Nat.Prime 11).dvd_mul.mp h11m) with h | h
    · norm_num at h
    · exact h
  have h17351 : 17351 ∣ d1 := by
    rcases ((by norm_num : Nat.Prime 17351).dvd_mul.mp h17351m) with h | h
    · norm_num at h
    · exact h
  exact ⟨h11, h17351⟩
