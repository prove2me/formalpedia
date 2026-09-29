-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:46:07.951561+00:00
-- url     : https://prove2.me/submissions/356c7c35-0087-4a35-a2ef-deaa2aede1b1

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_q4_127_absurd

theorem solution (p m d q4 sigma a b c e : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsigma_eq : sigma = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (hq4 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    False := by
  have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_role
    p m d q4 hp hm hpm hprod hsig hsupport h19mem h19exp
  rcases hrole with hp127 | hq4127
  · exact False.elim (OddPerfectNumber.k_one_p127_hprod_odd_square_absurd
      p m d hm hprod hp127)
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_q4_127_absurd
      p m d q4 sigma a b c e hp hm hpm hprod hsig hsigma_eq hsupport hq4prime
      hq4gt h19mem h19exp hD hpow hsigma h3 h19 hq4
