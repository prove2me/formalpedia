-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:13:47.320583+00:00
-- url     : https://prove2.me/submissions/bb77999b-7362-4060-9f44-7772ec395f7e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_51_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_57_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_69_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_87_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_115_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_129_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_141_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_205_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_187_absurd_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Weakened half-floor dispatch over the nine low-q4 middle cases.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  rcases hcases with h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_51_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_57_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_69_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_87_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_115_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_129_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_141_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_187_absurd_v1
      m _ _ hm hsupport hDm rfl rfl
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_205_abundance_v1
      m a b c e _ _ _ sigma hfac hsigma hrel rfl rfl rfl ha hb hc he
