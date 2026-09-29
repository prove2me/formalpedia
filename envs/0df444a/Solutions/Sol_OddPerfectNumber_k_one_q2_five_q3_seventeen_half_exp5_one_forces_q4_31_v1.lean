-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:06:01.391535+00:00
-- url     : https://prove2.me/submissions/f0c028c0-0d90-4155-b3ea-0ed442a008d5

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Disjunctive forces-conclusion: r=31 may equal q4 (cf. accepted b_one_forces_q4_31 pattern).
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
    b ≠ 1 ∨ q4 = 31 := by
  by_cases hb1 : b = 1
  · have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
    have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have h2b : 2 * b = 2 := by omega
    have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 5 hsq0 h5mem
    rw [h5exp, h2b] at hloc
    have hSeq : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) = 31 := by
      norm_num [Finset.sum_range_succ]
    rw [hSeq] at hloc
    have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
    have h31dvd : 31 ∣ ∑ x ∈ (m ^ 2).divisors, x := hloc
    have hprime : Nat.Prime 31 := by norm_num
    have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
      p m d 3 5 17 q4 31 hp hprime hm0 hsig hddvd h31dvd hsupport
    rcases hcase with h | h | h | h | h
    · subst h
      have hhalf : ((31 + 1) / 2) = 16 := by norm_num
      have h16prod : m ^ 2 = 16 * d := by
        calc m ^ 2 = ((31 + 1) / 2) * d := hprod
          _ = 16 * d := by rw [hhalf]
      have h2dvd : (2 : Nat) ∣ m ^ 2 := ⟨8 * d, by omega⟩
      have h2m : (2 : Nat) ∣ m := (Nat.prime_two.dvd_of_dvd_pow h2dvd)
      have heven : Even m := even_iff_two_dvd.mpr h2m
      exact False.elim ((Nat.not_even_iff_odd.mpr hm) heven)
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact Or.inr h.symm
  · exact Or.inl hb1
