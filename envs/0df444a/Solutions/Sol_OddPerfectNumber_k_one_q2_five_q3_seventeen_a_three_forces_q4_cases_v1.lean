-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_a_three_forces_q4_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:46:50.215058+00:00
-- url     : https://prove2.me/submissions/ded95251-cb40-44ab-b27f-16653ff7ecd1

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- a=3 means full exponent 6, sigma(3^6) = 1093, prime.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≠ 3 ∨ q4 = 1093 ∨ q4 = 547 := by
  by_cases ha3 : a = 3
  ·
    have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
    have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have h2a : 2 * a = 6 := by omega
    have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 3 hsq0 h3mem
    rw [h3exp, h2a] at hloc
    have hSeq : (∑ i ∈ Finset.range (6 + 1), 3 ^ i) = 1093 := by
      norm_num [Finset.sum_range_succ]
    rw [hSeq] at hloc
    have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
    have h1093dvd : 1093 ∣ ∑ x ∈ (m ^ 2).divisors, x := hloc
    have hprime : Nat.Prime 1093 := by norm_num
    have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
      p m d 3 5 17 q4 1093 hp hprime hm0 hsig hddvd h1093dvd hsupport
    rcases hcase with h | h | h | h | h
    · -- p = 1093: then D = 547 (prime) divides m^2, forcing 547 into support
      subst h
      have hhalf : ((1093 + 1) / 2) = 547 := by norm_num
      have h547 : m ^ 2 = 547 * d := by
        calc m ^ 2 = ((1093 + 1) / 2) * d := hprod
          _ = 547 * d := by rw [hhalf]
      have h547dvd : (547 : Nat) ∣ m ^ 2 := ⟨d, by omega⟩
      have h547prime : Nat.Prime 547 := by norm_num
      have h547m : (547 : Nat) ∣ m := h547prime.dvd_of_dvd_pow h547dvd
      have h547mem : 547 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h547prime, h547m, hm0⟩
      have hdis := hsupport 547 h547mem
      rcases hdis with h3 | h5 | h17 | hq
      · omega
      · omega
      · omega
      · exact Or.inr (Or.inr hq.symm)
    · omega
    · omega
    · omega
    · exact Or.inr (Or.inl h.symm)
  · exact Or.inl ha3
