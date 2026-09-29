-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exponent_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T16:30:10.867772+00:00
-- url     : https://prove2.me/submissions/69f5e8ee-74ec-45c3-be04-98d40af0a6e2

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp19_ge2_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
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
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e := by
  have ha4 := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  have hab := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  have hc2 := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp
    h19mem h19exp ha hb hc he
  exact ⟨ha4, hab.2, hc2, he⟩
