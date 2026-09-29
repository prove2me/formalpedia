-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_candidates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:55:09.760091+00:00
-- url     : https://prove2.me/submissions/6db533a1-4665-46c3-80c0-c42e0ba4aa6d

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_q4_mod3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_q4_mod5_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hD : D = 289) :
    q4 = 31 ∨ q4 = 61 ∨ q4 = 151 ∨ q4 = 181 ∨ q4 = 211 ∨ q4 = 241 ∨
      q4 = 271 ∨ q4 = 331 ∨ q4 = 421 := by
  have h3 : q4 % 3 = 1 :=
    k_one_q2_five_q3_seventeen_D289_q4_mod3_v1 m a b c e D p q4 sigma
      hfac hsigma hrel hp_eq hq4gt ha hD
  have h5 : q4 % 5 = 1 :=
    k_one_q2_five_q3_seventeen_D289_q4_mod5_v1 m a b c e D p q4 sigma
      hfac hsigma hrel hp_eq hq4gt hb hD
  have h500 : q4 < 500 :=
    k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1 m a b c e D p q4 sigma
      hfac hsigma hrel hp_eq hp hq4 hq4gt ha hb hc he hD
  have hdvd3 : 3 ∣ q4 - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hdvd5 : 5 ∣ q4 - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hdvd15 : 15 ∣ q4 - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) hdvd3 hdvd5
  obtain ⟨k, hk⟩ := hdvd15
  have hkq : q4 = 15 * k + 1 := by omega
  have hk33 : k ≤ 33 := by omega
  interval_cases k <;> (rw [hkq] at hq4 ⊢) <;> first
    | decide
    | (exfalso; norm_num at hq4)
