-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b1_q31_e1_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:20:39.976226+00:00
-- url     : https://prove2.me/submissions/8bcef0a1-9372-487c-afe6-7a9d9ff9a5b4

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
    (hq4mem : q4 ∈ (m ^ 2).primeFactors)
    (hq4exp : (m ^ 2).factorization q4 = 2*e)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hb1 : b = 1) (hq4eq : q4 = 31) (he1 : e = 1) :
    False := by
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  subst hq4eq
  have he2 : 2 * e = 2 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 31 hsq0 hq4mem
  rw [hq4exp, he2] at hloc
  have hSeq : (∑ i ∈ Finset.range (2 + 1), 31 ^ i) = 993 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have h331dvd : 331 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    (by norm_num : 331 ∣ 993).trans hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 31 331 hp (by norm_num) hm0 hsig hddvd h331dvd hsupport
  rcases hcase with h | h | h | h | h
  · -- 331 = p, so (p+1)/2 = 166 divides m^2, hence 2 divides m: against Odd m
    have hp331 : p = 331 := h.symm
    subst hp331
    norm_num at hprod
    have h2sq : 2 ∣ m ^ 2 := ⟨83 * d, by omega⟩
    have h2m : 2 ∣ m := (Nat.prime_two.prime).dvd_of_dvd_pow h2sq
    omega
  · omega
  · omega
  · omega
  · omega
