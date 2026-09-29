-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_q4_ne31_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:22:40.14879+00:00
-- url     : https://prove2.me/submissions/265acb33-3b29-4d85-88bc-abe62590d5b3

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2)
    (hq4ne : q4 ≠ 31) :
    False := by
  have hroles := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
    p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h5exp
  rcases hroles with hp31 | hq431
  · exact OddPerfectNumber.k_one_p31_hprod_odd_square_absurd p m d hm hprod hp31
  · exact hq4ne hq431
