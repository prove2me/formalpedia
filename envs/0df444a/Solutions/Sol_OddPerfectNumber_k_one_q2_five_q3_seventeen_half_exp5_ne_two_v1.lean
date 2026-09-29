-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_two_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:32:08.305003+00:00
-- url     : https://prove2.me/submissions/57e26ac2-f4e1-404c-9294-b67cd63f785b

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- b=2 means full exponent 4, sigma(5^4) = 781 = 11 * 71; use 11 < q4.
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
    b ≠ 2 := by
  intro hb2
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h2b : 2 * b = 4 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 5 hsq0 h5mem
  rw [h5exp, h2b] at hloc
  have hSeq : (∑ i ∈ Finset.range (4 + 1), 5 ^ i) = 781 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have h11dvd : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    (by norm_num : 11 ∣ 781).trans hloc
  have hprime : Nat.Prime 11 := by norm_num
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 17 q4 11 hp hprime hm0 hsig hddvd h11dvd hsupport
  rcases hcase with h | h | h | h | h
  · -- p = 11: then D = 6 is even, forcing 2 ∣ m against Odd m
    subst h
    have hhalf : ((11 + 1) / 2) = 6 := by norm_num
    have h6 : m ^ 2 = 6 * d := by
      calc m ^ 2 = ((11 + 1) / 2) * d := hprod
        _ = 6 * d := by rw [hhalf]
    have h2dvd : (2 : Nat) ∣ m ^ 2 := ⟨3 * d, by omega⟩
    have h2prime : Nat.Prime 2 := by norm_num
    have h2m : (2 : Nat) ∣ m := h2prime.dvd_of_dvd_pow h2dvd
    obtain ⟨k, hk⟩ := hm
    omega
  · omega
  · omega
  · omega
  · omega
