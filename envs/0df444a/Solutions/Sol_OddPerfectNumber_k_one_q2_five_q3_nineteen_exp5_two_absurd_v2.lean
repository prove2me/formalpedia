-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:20:22.862024+00:00
-- url     : https://prove2.me/submissions/92d3e9b7-2f8d-4179-badb-e8c1b74ae744

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_forces_q4_31
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd_v2

theorem solution (p m d sigma q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hsupport_m : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31)) :
    False := by
  have hq431 := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_forces_q4_31
    p m d q4 hp hp4 hm hpm hprod hsig hsupport_m hq4prime hq4gt h5mem h5exp
  subst q4
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd_v2
    p m d sigma hp hp4 hm hpm hprod hsig hsupport hupper hsigma h3mem h3pos
    h3even h19pos h19even h31pos h31even h5exp
