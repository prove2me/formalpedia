-- Prove2me | solution 1 for OddPerfectNumber.Kernel.order_one_length_five_forces_p_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:43:00.912985+00:00
-- url     : https://prove2.me/submissions/f08cd8e0-2825-41b6-b37f-86a4cf2efb55

import Mathlib

theorem solution (p q : Nat) (hp : p.Prime)
    (hqmod : q % p = 1)
    (hsrc : p ∣ ∑ i ∈ Finset.range 5, q ^ i) :
    p = 5 := by
  have hmod : (∑ i ∈ Finset.range 5, q ^ i) % p = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hsrc
  have hqpow : ∀ n : Nat, q ^ n % p = 1 := by
    intro n
    have hp1 : 1 < p := hp.one_lt
    induction n with
    | zero => simp [Nat.mod_eq_of_lt hp1]
    | succ n ih =>
        simp [pow_succ, Nat.mul_mod, hqmod, ih, Nat.mod_eq_of_lt hp1]
  have hs : (∑ i ∈ Finset.range 5, q ^ i) % p = 5 % p := by
    by_cases hp_le : p ≤ 5
    · have hp2 : 2 ≤ p := hp.two_le
      have hcases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
      rcases hcases with h2 | hrest
      · subst p
        norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod, hqmod]
      · rcases hrest with h3 | hrest
        · subst p
          norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod, hqmod]
        · rcases hrest with h4 | h5
          · subst p
            norm_num at hp
          · subst p
            norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod, hqmod]
    · have hp5 : 5 < p := by omega
      have h2mod : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
      have h1mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
      have h4mod : 4 % p = 4 := Nat.mod_eq_of_lt (by omega)
      have h5mod : 5 % p = 5 := Nat.mod_eq_of_lt hp5
      norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod,
        hqmod, h2mod, h1mod, h3mod, h4mod, h5mod, Nat.mod_eq_of_lt hp5]
  have hpdiv : p ∣ 5 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    calc
      5 % p = (∑ i ∈ Finset.range 5, q ^ i) % p := hs.symm
      _ = 0 := hmod
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hpdiv with h1 | h5
  · exact (hp.ne_one h1).elim
  · exact h5
