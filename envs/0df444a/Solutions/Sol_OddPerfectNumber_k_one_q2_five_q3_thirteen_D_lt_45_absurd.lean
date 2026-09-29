-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:17:11.119642+00:00
-- url     : https://prove2.me/submissions/7dfc847d-a46d-4caa-8ab7-06fddee54fe1

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_small_exponents_absurd

theorem solution (p m d D q4 sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 ∨ (m ^ 2).factorization 5 = 6)
    (hD : D < 45) :
    False := by
  exact OddPerfectNumber.k_one_q2_five_q3_thirteen_small_exponents_absurd
    p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h5exp
