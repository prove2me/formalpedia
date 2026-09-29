-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp3_ne_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:19:04.576694+00:00
-- url     : https://prove2.me/submissions/2a045168-e0e9-408c-9ff7-c3d095e8aa08

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
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
    a ≠ 1 := by
  intro ha1
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h2a : 2 * a = 2 := by omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 3 hsq0 h3mem
  rw [h3exp, h2a] at hloc
  have hSeq : (∑ i ∈ Finset.range (2 + 1), 3 ^ i) = 13 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have h13dvd : 13 ∣ ∑ x ∈ (m ^ 2).divisors, x := hloc
  have hprime : Nat.Prime 13 := by norm_num
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 17 q4 13 hp hprime hm0 hsig hddvd h13dvd hsupport
  rcases hcase with h | h | h | h | h
  · -- p = 13: then D = 7 divides m^2, forcing 7 into support
    subst h
    have hhalf : ((13 + 1) / 2) = 7 := by norm_num
    have h7prod : m ^ 2 = 7 * d := by
      calc m ^ 2 = ((13 + 1) / 2) * d := hprod
        _ = 7 * d := by rw [hhalf]
    have h7dvd : (7 : Nat) ∣ m ^ 2 := ⟨d, by omega⟩
    have h7prime : Nat.Prime 7 := by norm_num
    have h7m : (7 : Nat) ∣ m := h7prime.dvd_of_dvd_pow h7dvd
    have h7mem : 7 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h7prime, h7m, hm0⟩
    have hdis := hsupport 7 h7mem
    rcases hdis with h3 | h5 | h17 | hq
    · omega
    · omega
    · omega
    · omega
  · omega
  · omega
  · omega
  · omega
