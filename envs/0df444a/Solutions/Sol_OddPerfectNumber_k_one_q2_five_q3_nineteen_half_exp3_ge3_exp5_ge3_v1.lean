-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T10:11:52.947184+00:00
-- url     : https://prove2.me/submissions/f8c1548e-6ae7-47a9-828d-e10f337a25ea

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_monotone

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; imported children use FULL exponents.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    3 ≤ a ∧ 3 ≤ b := by
  have ha1 : a ≠ 1 := by
    intro h
    have hx : (m ^ 2).factorization 3 = 2 := by simpa [h] using h3exp
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_absurd
      p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h3mem hx
  have ha2 : a ≠ 2 := by
    intro h
    have hx : (m ^ 2).factorization 3 = 4 := by simpa [h] using h3exp
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h3mem hx
  have ha3 : 3 ≤ a := by omega
  have hupper : sigma ≤ 2 * m ^ 2 := by
    have hhalf : p ≤ 2 * ((p + 1) / 2) := by omega
    calc
      sigma = p * d := hglobal.trans hsig
      _ ≤ (2 * ((p + 1) / 2)) * d := Nat.mul_le_mul_right d hhalf
      _ = 2 * m ^ 2 := by rw [hprod]; ring
  have hb1 : b ≠ 1 := by
    intro h
    have hx : (m ^ 2).factorization 5 = 2 := by simpa [h] using h5exp
    have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
      p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h5mem hx
    rcases hrole with hp31 | hq31
    · norm_num [hp31] at hp4
    · have hab := OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_monotone
        (2*a) (2*c) (2*e) (by omega) (by omega) (by omega)
      have hf : m ^ 2 = 3 ^ (2*a) * 5 ^ 2 * 19 ^ (2*c) * 31 ^ (2*e) := by
        simpa only [h, hq31, Nat.mul_one] using hfac
      have hs : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
          (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
          (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
          (∑ i ∈ Finset.range (2*e + 1), 31 ^ i) := by
        simpa only [h, hq31, Nat.mul_one] using hsigma
      rw [← hf, ← hs] at hab
      omega
  have hb2 : b ≠ 2 := by
    intro h
    have hx : (m ^ 2).factorization 5 = 4 := by simpa [h] using h5exp
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem hx
  exact ⟨ha3, by omega⟩
