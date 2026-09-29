-- Prove2me | solution 1 for OddPerfectNumber.k_one_four_support_second_prime_le_23
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:03:58.214708+00:00
-- url     : https://prove2.me/submissions/c7e6bfb0-fc2b-409b-976c-e90640ef5ec0

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_four_support_second_le_23

open OddPerfectNumber

theorem solution (p m d q1 q2 q3 q4 : Nat)
  (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
  (hprod : m ^ 2 = ((p + 1) / 2) * d)
  (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
  (hsupport : m.primeFactors = {q1, q2, q3, q4})
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime) (hq4 : q4.Prime)
  (horder : q1 < q2 ∧ q2 < q3 ∧ q3 < q4)
  (hq1eq : q1 = 3) :
    q2 ≤ 23 :=
  OddPerfectNumber.k_one_four_support_second_le_23 p m d q1 q2 q3 q4 hp hp4 hm hpm hprod hsig hsupport hq1 hq2 hq3 hq4 horder hq1eq
