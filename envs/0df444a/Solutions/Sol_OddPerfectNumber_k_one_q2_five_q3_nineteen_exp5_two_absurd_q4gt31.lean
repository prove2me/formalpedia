-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:16:52.258306+00:00
-- url     : https://prove2.me/submissions/fb566fe1-0261-4207-9599-aeb098403c92

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by
  have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
    p m d q4 hp hm hpm hprod hsig hsupport hq4prime (by omega) h5mem h5exp
  rcases hrole with hp31 | hq431
  · subst p
    norm_num at hp4
  · omega
