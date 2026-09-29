-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:50:59.320181+00:00
-- url     : https://prove2.me/submissions/06ef0803-4037-4544-b0dc-a2ff9db04d47

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp3_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp3_ne_two_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_a_three_forces_q4_cases_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Pure-logic combiner over three Proved children; no new number theory.
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
    4 ≤ a ∨ q4 = 1093 ∨ q4 = 547 := by
  have hne1 := OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp3_ne_one_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he
  have hne2 := OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp3_ne_two_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he
  have hcases := OddPerfectNumber.k_one_q2_five_q3_seventeen_a_three_forces_q4_cases_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he
  rcases hcases with h3 | h1093 | h547
  · have h4 : 4 ≤ a := by omega
    exact Or.inl h4
  · exact Or.inr (Or.inl h1093)
  · exact Or.inr (Or.inr h547)
