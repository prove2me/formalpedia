-- Prove2me | solution 1 for OddPerfectNumber.Kernel.middle_source_exp_two_forces_5_31_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:09:39.611275+00:00
-- url     : https://prove2.me/submissions/2d159334-107e-4199-9c32-df5e0c1a60d7

import Mathlib

theorem solution (p qC qD a b u : Nat)
    (hp : p.Prime)
    (hu : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = qC * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * (qD * b ^ 2))
    (hqC : qC.Prime)
    (hqD : qD.Prime)
    (hqCmod : qC % p = 1)
    (hsource : p ∣ ∑ i ∈ Finset.range 5, qC ^ i) :
    p = 5 ∧ qC = 31 ∧ qD = 7 ∧ a = 1 ∧ b = 1 := by
  have hqpow : ∀ n : Nat, qC ^ n % p = 1 := by
    intro n
    have hp1 : 1 < p := by omega
    induction n with
    | zero => simp [Nat.mod_eq_of_lt hp1]
    | succ n ih =>
        simp [pow_succ, Nat.mul_mod, hqCmod, ih, Nat.mod_eq_of_lt hp1]
  have hmod : (∑ i ∈ Finset.range 5, qC ^ i) % p = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hsource
  have hsum : (∑ i ∈ Finset.range 5, qC ^ i) % p = 5 % p := by
    have hp1 : 1 < p := by omega
    by_cases hp_le : p ≤ 5
    · have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 := by omega
      rcases hp_cases with hp2eq | hp3eq | hp5eq
      · subst p
        norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod,
          hqCmod]
      · subst p
        norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod,
          hqCmod]
      · subst p
        norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod,
          hqCmod]
    · have hp5 : 5 < p := by omega
      have h2mod : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
      have h1mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
      have h4mod : 4 % p = 4 := Nat.mod_eq_of_lt (by omega)
      have h5mod : 5 % p = 5 := Nat.mod_eq_of_lt hp5
      norm_num [Finset.sum_range_succ, pow_succ, Nat.add_mod, Nat.mul_mod,
        hqCmod, h2mod, h1mod, h3mod, h4mod, h5mod, Nat.mod_eq_of_lt hp5]
  have hpdiv : p ∣ 5 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    calc
      5 % p = (∑ i ∈ Finset.range 5, qC ^ i) % p := hsum.symm
      _ = 0 := hmod
  have hp_le : p ≤ 5 := Nat.le_of_dvd (by norm_num) hpdiv
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 := by omega
  have hp5 : p = 5 := by
    rcases hp_cases with h2 | h3 | h5
    · subst p
      omega
    · subst p
      omega
    · exact h5
  subst p
  norm_num at hC hD hqCmod
  have hqCdiv : qC ∣ 31 := ⟨a ^ 2, hC⟩
  have hqCle : qC ≤ 31 := Nat.le_of_dvd (by norm_num) hqCdiv
  have hqCeq : qC = 31 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hqCdiv with h1 | h31
    · exact (hqC.ne_one h1).elim
    · exact h31
  have ha2 : a ^ 2 = 1 := by
    rw [hqCeq] at hC
    omega
  have ha : a = 1 := by nlinarith
  have hqDdiv : qD ∣ 7 := by
    have hD' : 7 = qD * b ^ 2 := by omega
    exact ⟨b ^ 2, hD'⟩
  have hqDle : qD ≤ 7 := Nat.le_of_dvd (by norm_num) hqDdiv
  have hqDeq : qD = 7 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hqDdiv with h1 | h7
    · exact (hqD.ne_one h1).elim
    · exact h7
  have hb2 : b ^ 2 = 1 := by
    rw [hqDeq] at hD
    omega
  have hb : b = 1 := by nlinarith
  exact ⟨rfl, hqCeq, hqDeq, ha, hb⟩
