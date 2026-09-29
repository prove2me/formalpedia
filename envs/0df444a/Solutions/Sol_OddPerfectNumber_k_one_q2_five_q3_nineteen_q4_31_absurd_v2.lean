-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T01:40:56.78828+00:00
-- url     : https://prove2.me/submissions/597cfb57-96bd-49ee-ad5a-dbb3c14cd68f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_of_factorization
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion

theorem solution (p m d sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31))
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by
  have hm0 : m ≠ 0 := by
    obtain ⟨u, hu⟩ := hm
    omega
  have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hfac : m ^ 2 =
      3 ^ ((m ^ 2).factorization 3) *
        5 ^ ((m ^ 2).factorization 5) *
        19 ^ ((m ^ 2).factorization 19) *
        31 ^ ((m ^ 2).factorization 31) := by
    exact OddPerfectNumber.four_support_factorization_expansion
      (m ^ 2) 3 5 19 31 hm2ne hsupport
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  rw [h5exp] at hfac
  have hm2support : (m ^ 2).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_pow m (by norm_num)]
  have h3support : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = 31 := by
    intro x hx
    rw [← hm2support] at hx
    rw [hsupport] at hx
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  have ha : 6 ≤ (m ^ 2).factorization 3 := by
    by_contra h
    have hle : (m ^ 2).factorization 3 ≤ 5 := by omega
    rcases h3even with ⟨u, hu⟩
    have hcases : (m ^ 2).factorization 3 = 2 ∨
        (m ^ 2).factorization 3 = 4 := by omega
    rcases hcases with h2 | h4
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_absurd
        p m d 31 hp hm hpm hprod hsig h3support (by norm_num)
        (by omega) h3mem h2
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_four_absurd
        p m d 31 hp hp4 hm hpm hprod hsig h3support (by norm_num)
        (by omega) h3mem h4
  have hc : 2 ≤ (m ^ 2).factorization 19 := by
    rcases h19even with ⟨u, hu⟩
    omega
  have he : 2 ≤ (m ^ 2).factorization 31 := by
    rcases h31even with ⟨u, hu⟩
    omega
  exact OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_of_factorization
    m ((m ^ 2).factorization 3) ((m ^ 2).factorization 19)
      ((m ^ 2).factorization 31) sigma hfac hsigma hupper ha hc he
