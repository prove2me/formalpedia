-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ge_four_smallq4_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:22:34.083109+00:00
-- url     : https://prove2.me/submissions/7d7444cb-b814-4b03-a508-7ee5806fa6d6

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_two_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_three_smallq4_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Range-local composition: b >= 4 (half-exp) under q4 <= 89, from b!=1, b!=2, b!=3.
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
    4 ≤ b := by
  have h1 := OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
    p m d q4 a b c e sigma hp hm hprod hsig hsupport hfac hsigma hglobal
    h5mem h5exp ha hb hc he
  have h2 := OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_two_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h13mem h13exp ha hb hc he
  have h3 := OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_three_smallq4_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hq4le
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h13mem h13exp ha hb hc he
  omega
