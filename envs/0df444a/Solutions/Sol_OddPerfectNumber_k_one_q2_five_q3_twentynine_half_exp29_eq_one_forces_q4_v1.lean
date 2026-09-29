-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp29_eq_one_forces_q4_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:58:11.422015+00:00
-- url     : https://prove2.me/submissions/6484dbb6-fe9f-4607-aa18-3ae3cd070506

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hc1 : c = 1) :
    q4 = 67 := by
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h2c : 2 * c = 2 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 29 hsq0 h29mem
  rw [h29exp, h2c] at hloc
  have hSeq : (∑ i ∈ Finset.range (2 + 1), 29 ^ i) = 871 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have h13dvd : 13 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    (by norm_num : 13 ∣ 871).trans hloc
  have h67dvd : 67 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    (by norm_num : 67 ∣ 871).trans hloc
  have c13 := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 q4 13 hp (by norm_num) hm0 hsig hddvd h13dvd hsupport
  have c67 := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 q4 67 hp (by norm_num) hm0 hsig hddvd h67dvd hsupport
  -- The 13-arm forces p = 13 (13 cannot be 3, 5, 29, or q4 > 29).
  have hp13 : p = 13 := by
    rcases c13 with h | h | h | h | h
    · exact h.symm
    · omega
    · omega
    · omega
    · omega
  -- The 67-arm then leaves only q4 = 67 (67 = p contradicts p = 13).
  rcases c67 with h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · exact h.symm
