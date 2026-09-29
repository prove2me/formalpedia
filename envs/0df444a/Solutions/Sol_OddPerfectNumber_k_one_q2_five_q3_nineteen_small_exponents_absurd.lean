-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_exponents_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:38:57.762755+00:00
-- url     : https://prove2.me/submissions/41257465-980d-4c47-962c-e226cd1ef397

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_four_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 151 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2 ∨
      (m ^ 2).factorization 19 = 4) :
    False := by
  rcases h19exp with h2 | h4
  · have hq4gt' : 127 < q4 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_two_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt'
      h19mem h2
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h19mem h4
