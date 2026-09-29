-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_self_cases_with_q4_dvd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T18:42:25.210343+00:00
-- url     : https://prove2.me/submissions/4d846e44-d8f8-4335-a97f-a120a613a6d5

import Mathlib
import Theorems.Thm_OddPerfectNumber_q3_nineteen_prime_pair_142_224_cases_v1

theorem solution (D p q4 : Nat) (hDlow : 147 ≤ D) (hDlt : D < 225)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4ge : 142 ≤ q4) (hq4leD : q4 ≤ D) (hq4dvd : q4 ∣ D) :
    (D = 157 ∧ q4 = 157 ∧ p = 313) ∨
      (D = 199 ∧ q4 = 199 ∧ p = 397) ∨
      (D = 211 ∧ q4 = 211 ∧ p = 421) := by
  obtain ⟨t, ht⟩ := hq4dvd
  have htpos : 1 ≤ t := by
    by_contra h
    have ht0 : t = 0 := by omega
    have hD0 : D = 0 := by
      calc
        D = q4 * t := ht
        _ = 0 := by simp [ht0]
    omega
  have htone : t = 1 := by
    by_contra hne
    have htge : 2 ≤ t := by omega
    have hmul : q4 * 2 ≤ q4 * t := Nat.mul_le_mul_left q4 htge
    have hmulD : q4 * 2 ≤ D := by
      exact hmul.trans_eq ht.symm
    omega
  have hDq : D = q4 := by
    calc
      D = q4 * t := ht
      _ = q4 := by simp [htone]
  have hpq : p = 2 * q4 - 1 := by omega
  have hq4upper : q4 ≤ 224 := by omega
  have hcases := OddPerfectNumber.q3_nineteen_prime_pair_142_224_cases_v1
    q4 p hq4prime hp hpq hq4ge hq4upper
  rcases hcases with h157 | h199 | h211
  · exact Or.inl ⟨by omega, h157, by omega⟩
  · exact Or.inr (Or.inl ⟨by omega, h199, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, h211, by omega⟩)
