-- Prove2me | solution 1 for OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T10:53:08.124606+00:00
-- url     : https://prove2.me/submissions/54c59a2f-3a41-4425-a500-712ac463ddec

import Mathlib

theorem solution (q a : Nat) (hq : q.Prime) :
    ¬ q ∣ ∑ i ∈ Finset.range (a + 1), q ^ i := by
  intro hdiv
  have hmod : ∀ n : Nat,
      (∑ i ∈ Finset.range (n + 1), q ^ i) % q = 1 := by
    intro n
    induction n with
    | zero => simp [Nat.mod_eq_of_lt hq.one_lt]
    | succ n ih =>
        rw [Finset.sum_range_succ]
        simp [ih, pow_succ, Nat.add_mod, Nat.mul_mod,
          Nat.mod_eq_of_lt hq.one_lt]
  have hz := Nat.mod_eq_zero_of_dvd hdiv
  rw [hmod a] at hz
  omega
