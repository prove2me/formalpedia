-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_e_one_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:20:55.957345+00:00
-- url     : https://prove2.me/submissions/fdeb6b51-44b7-47f2-a8a2-663e3bd8f888

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1

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
    (hb1 : b = 1) (he1 : e = 1) :
    False := by
  -- In the canonical q3 = 29 four-support coordinates the 5-half-exponent is never 1
  -- (proved sibling `k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1`), which contradicts
  -- the branch hypothesis `hb1 : b = 1`.  The branch hypothesis `he1 : e = 1` is not needed.
  have hbne : b ≠ 1 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1
      p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  exact hbne hb1
