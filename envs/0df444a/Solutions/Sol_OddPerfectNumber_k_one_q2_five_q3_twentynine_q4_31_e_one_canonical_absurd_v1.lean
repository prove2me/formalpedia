-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_q4_31_e_one_canonical_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T04:45:51.537995+00:00
-- url     : https://prove2.me/submissions/702f6334-87a7-4992-a47a-3a56b51d987f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_q4_31_e_one_331_dvd_sigma_v1
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

open OddPerfectNumber

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
    (hq4eq : q4 = 31) (he1 : e = 1) :
    False := by
  subst hq4eq
  subst he1
  rw [show (2 * 1 + 1) = 3 from rfl] at hsigma
  have h331 : 331 ∣ sigma :=
    k_one_q2_five_q3_twentynine_q4_31_e_one_331_dvd_sigma_v1 a b c sigma hsigma
  have h331sum : 331 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    rw [← hglobal]; exact h331
  have h331p : Nat.Prime 331 := by norm_num
  obtain ⟨kodd, hkodd⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hrole := four_support_sigma_prime_restricted p m d 3 5 29 31 331
    hp h331p hm0 hsig hddvd h331sum hsupport
  rcases hrole with h | h | h | h | h
  · have hp331 : p = 331 := h.symm
    have h166 : (p + 1) / 2 = 166 := by omega
    rw [h166] at hprod
    have h83dvd : 83 ∣ m ^ 2 := ⟨2 * d, by rw [hprod]; ring⟩
    have h83p : Nat.Prime 83 := by norm_num
    have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have h83dvd_m : 83 ∣ m :=
      (Nat.prime_iff.mp h83p).dvd_of_dvd_pow h83dvd
    have h83mem_m : 83 ∈ m.primeFactors :=
      (Nat.mem_primeFactors).mpr ⟨h83p, h83dvd_m, hm0⟩
    have h83sup := hsupport 83 h83mem_m
    omega
  · omega
  · omega
  · omega
  · omega
