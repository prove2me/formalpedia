-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp3_ne_four_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T13:42:11.010982+00:00
-- url     : https://prove2.me/submissions/057f2e7c-9d11-4153-964d-a91192b538ba

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 31 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 31 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h31mem : 31 ∈ (m ^ 2).primeFactors)
    (h31exp : (m ^ 2).factorization 31 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≠ 4 := by
  intro ha4
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h8a : 2 * a = 8 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 3 hsq0 h3mem
  rw [h3exp, h8a] at hloc
  have hSeq : (∑ i ∈ Finset.range (8 + 1), 3 ^ i) = 9841 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have h13dvd : 13 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    (by norm_num : 13 ∣ 9841).trans hloc
  have hprime : Nat.Prime 13 := by norm_num
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 31 q4 13 hp hprime hm0 hsig hddvd h13dvd hsupport
  rcases hcase with h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
