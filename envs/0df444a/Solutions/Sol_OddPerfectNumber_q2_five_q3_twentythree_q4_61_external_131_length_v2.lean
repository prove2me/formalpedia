-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentythree_q4_61_external_131_length_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T04:07:42.88509+00:00
-- url     : https://prove2.me/submissions/4729315a-db19-44a1-8782-0b768f189bcd

import Mathlib

theorem solution (e : Nat)
    (h : 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 61 ^ i) :
    5 ∣ 2 * e + 1 := by
  have hmod : ∀ n : Nat,
      (∑ i ∈ Finset.range n, 61 ^ i) % 5 = n % 5 := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
        rw [Finset.sum_range_succ]
        have hpow : 61 ^ n % 5 = 1 := by
          simp [Nat.pow_mod]
        simp [Nat.add_mod, ihn, hpow]
  have hz := Nat.mod_eq_zero_of_dvd h
  rw [hmod (2 * e + 1)] at hz
  exact Nat.dvd_of_mod_eq_zero hz
