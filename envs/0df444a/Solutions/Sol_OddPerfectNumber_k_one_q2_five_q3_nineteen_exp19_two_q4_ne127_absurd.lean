-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:13:14.911263+00:00
-- url     : https://prove2.me/submissions/63ec72ff-f516-40a3-97fb-c999eaa5b2c0

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2)
    (hq4ne : q4 ≠ 127) :
    False := by
  have hroles := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_role
    p m d q4 hp hm hpm hprod hsig hsupport h19mem h19exp
  rcases hroles with hp127 | hq4127
  · exact OddPerfectNumber.k_one_p127_hprod_odd_square_absurd p m d hm hprod hp127
  · exact hq4ne hq4127
