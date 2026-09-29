-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_three_smallq4_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:18:58.146654+00:00
-- url     : https://prove2.me/submissions/4407ef8b-e7ae-41e8-b9e7-7ee2eb64fd14

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- REDUCED helper: carries range-local q4 <= 89 premise for the middle range.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h13mem : 13 ∈ (m ^ 2).primeFactors)
    (h13exp : (m ^ 2).factorization 13 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 3 := by
  intro hb3
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h6b : 2 * b = 6 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 5 hsq0 h5mem
  rw [h5exp, h6b] at hloc
  have hSeq : (∑ i ∈ Finset.range (6 + 1), 5 ^ i) = 19531 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 13 q4 19531 hp (by norm_num) hm0 hsig hddvd hloc hsupport
  rcases hcase with h | h | h | h | h
  · -- 19531 = p, but 19531 % 4 = 3 contradicts p % 4 = 1
    have hp19531 : p = 19531 := h.symm
    have hmod : 19531 % 4 = 3 := by norm_num
    omega
  · omega
  · omega
  · omega
  · omega
