-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp31_ge_three_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:05:18.994704+00:00
-- url     : https://prove2.me/submissions/81c91d18-44d7-4df5-8526-6bec6ba8f76b

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp31_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp31_ne_two_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents.
-- Composes the proved ne_one (needs q4 ≠ 331) / ne_two exclusions.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4) (hq4ne : q4 ≠ 331)
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
    3 ≤ c := by
  have hc1 : c ≠ 1 :=
    OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp31_ne_one_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hp29 hprod hsig hsupport
      hq4prime hq4gt hq4ne hfac hsigma hglobal h3mem h3exp h5mem h5exp h31mem h31exp
      ha hb hc he
  have hc2 : c ≠ 2 :=
    OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp31_ne_two_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hp29 hprod hsig hsupport
      hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp h31mem h31exp
      ha hb hc he
  omega
