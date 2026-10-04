-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_odd_mult_unique_of_non_square
-- status  : ACCEPTED   (disprove)
-- author  : @os0xcom
-- created : 2026-10-03T16:09:21.699225+00:00
-- url     : https://prove2.me/submissions/0a7fbeba-a094-407e-b015-681b6d6f8230

import Mathlib

set_option linter.unusedVariables false

theorem solution :
    ¬ (∀ {a b q r : Nat} (_ha0 : a != 0) (_hb0 : b != 0) (_hab : Nat.gcd a b = 1)
        (_hq : q.Prime) (_hr : r.Prime) (_hqr : q != r)
        (_hsq : ∃ y : Nat, y ^ 2 = q * r * a * b) (_hna : ¬ ∃ y : Nat, y ^ 2 = a),
        ∃ t : Nat, t.Prime ∧ ¬ Even (a.factorization t) ∧
          ∀ z : Nat, z != t → Even (a.factorization z)) := by
  intro H
  have hsq : ∃ y : Nat, y ^ 2 = 3 * 5 * 15 * 1 := ⟨15, by norm_num⟩
  have hna : ¬ ∃ y : Nat, y ^ 2 = 15 := by
    rintro ⟨y, hy⟩
    rcases Nat.lt_trichotomy y 4 with hlt | heq | hgt
    · interval_cases y <;> norm_num at hy
    · norm_num [heq] at hy
    · have hmul := Nat.mul_le_mul hgt hgt
      have : y * y = 15 := by simpa [Nat.pow_two] using hy
      omega
  have h := H (a := 15) (b := 1) (q := 3) (r := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsq hna
  rcases h with ⟨t, ht, hodd, hall⟩
  have hprime3 : Nat.Prime 3 := by decide
  have hprime5 : Nat.Prime 5 := by decide
  have h15 : (15 : Nat) ≠ 0 := by decide
  have hv3 : (15).factorization 3 = 1 := by
    have hle : 1 ≤ (15).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hprime3 h15).mp (by decide : 3 ^ 1 ∣ 15)
    have hnot : ¬ 3 ^ 2 ∣ 15 := by decide
    have hlt : (15).factorization 3 < 2 := by
      by_contra hge
      exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization hprime3 h15).mpr (Nat.le_of_not_lt hge))
    omega
  have hv5 : (15).factorization 5 = 1 := by
    have hle : 1 ≤ (15).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hprime5 h15).mp (by decide : 5 ^ 1 ∣ 15)
    have hnot : ¬ 5 ^ 2 ∣ 15 := by decide
    have hlt : (15).factorization 5 < 2 := by
      by_contra hge
      exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization hprime5 h15).mpr (Nat.le_of_not_lt hge))
    omega
  have hodd3 : ¬ Even ((15).factorization 3) := by rw [hv3]; decide
  have hodd5 : ¬ Even ((15).factorization 5) := by rw [hv5]; decide
  by_cases ht3 : t = 3
  · have h5e : Even ((15).factorization 5) := by
      have hne : ((5 : Nat) != t) = true := by simp [ht3]
      simpa [hv5] using hall 5 hne
    exact hodd5 h5e
  · have h3e : Even ((15).factorization 3) := by
      have hne : ((3 : Nat) != t) = true := by
        have hneq : (3 : Nat) ≠ t := by
          intro h
          exact ht3 h.symm
        simpa [bne, beq_eq_false_iff_ne] using hneq
      simpa [hv3] using hall 3 hne
    exact hodd3 h3e
