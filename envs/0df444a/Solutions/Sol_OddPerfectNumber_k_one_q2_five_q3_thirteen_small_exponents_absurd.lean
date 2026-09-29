-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_small_exponents_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:25:48.725465+00:00
-- url     : https://prove2.me/submissions/f82894f2-4409-400c-a87e-ddfd941d2350

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_six_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 ∨
      (m ^ 2).factorization 5 = 6) :
    False := by
  rcases h5exp with h2 | h4 | h6
  · have hq4gt' : 31 < q4 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_two_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt'
      h5mem h2
  · have hq4gt' : 13 < q4 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt'
      h5mem h4
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_six_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h6
