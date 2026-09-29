-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_eq_one_forces_q4_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:56:38.17268+00:00
-- url     : https://prove2.me/submissions/e50c7f16-bbce-45f7-a1c8-8bc8a1e15fe5

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
    (hb1 : b = 1) :
    q4 = 31 := by
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h2b : 2 * b = 2 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 5 hsq0 h5mem
  rw [h5exp, h2b] at hloc
  have hSeq : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) = 31 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 q4 31 hp (by norm_num) hm0 hsig hddvd hloc hsupport
  rcases hcase with h | h | h | h | h
  · -- 31 = p, so (p+1)/2 = 16 divides m^2, hence 2 divides m: against Odd m
    have hp31 : p = 31 := h.symm
    have h16eq : (31 + 1) / 2 = 16 := by norm_num
    rw [hp31, h16eq] at hprod
    have h2sq : 2 ∣ m ^ 2 := ⟨8 * d, by rw [hprod]; ring⟩
    have h2m : 2 ∣ m := (Nat.prime_two.prime).dvd_of_dvd_pow h2sq
    obtain ⟨k, hk⟩ := hm
    obtain ⟨j, hj⟩ := h2m
    omega
  · omega
  · omega
  · omega
  · exact h.symm
