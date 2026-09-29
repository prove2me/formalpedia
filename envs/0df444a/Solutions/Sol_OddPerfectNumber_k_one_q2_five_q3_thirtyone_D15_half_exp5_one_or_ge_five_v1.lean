-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_one_or_ge_five_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:00:07.808808+00:00
-- url     : https://prove2.me/submissions/1fad58b4-151e-4989-9db2-e335a0affa02

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_two_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_three_midq4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_four_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents.
-- Composes the proved ne_two / ne_three_midq4 / ne_four exclusions.
-- b = 1 remains a separate case branch (b1-bound gives q4 ≤ 170 there).
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4) (hq4lt : q4 < 19531)
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
    b = 1 ∨ 5 ≤ b := by
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  · right
    have hb2 : b ≠ 2 :=
      OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_two_v1
        p m d q4 a b c e sigma hp hp4 hm hpm hp29 hprod hsig hsupport
        hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp h31mem h31exp
        ha hb hc he
    have hb3 : b ≠ 3 :=
      OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_three_midq4_v1
        p m d q4 a b c e sigma hp hp4 hm hpm hp29 hprod hsig hsupport
        hq4prime hq4gt hq4lt hfac hsigma hglobal h3mem h3exp h5mem h5exp h31mem h31exp
        ha hb hc he
    have hb4 : b ≠ 4 :=
      OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_four_v1
        p m d q4 a b c e sigma hp hp4 hm hpm hp29 hprod hsig hsupport
        hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp h31mem h31exp
        ha hb hc he
    omega
