-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:56:49.10969+00:00
-- url     : https://prove2.me/submissions/d122beca-4a81-4c05-8001-67922f5dcc5c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_c_one_forces_q4_307_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_c_two_forces_q4_cases_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Pure-logic combiner over two Proved children; no new number theory.
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
    3 ≤ c ∨ q4 = 307 ∨ q4 = 88741 ∨ q4 = 44371 := by
  have h1 := OddPerfectNumber.k_one_q2_five_q3_seventeen_c_one_forces_q4_307_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he
  have h2 := OddPerfectNumber.k_one_q2_five_q3_seventeen_c_two_forces_q4_cases_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he
  rcases h1 with hc1 | h307
  · rcases h2 with hc2 | h88 | h44
    · have h3 : 3 ≤ c := by omega
      exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inl h88))
    · exact Or.inr (Or.inr (Or.inr h44))
  · exact Or.inr (Or.inl h307)
