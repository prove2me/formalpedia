-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt31
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:13:29.653829+00:00
-- url     : https://prove2.me/submissions/71a5099f-abab-4b2d-b34c-45ec905757d3

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5even : Even ((m ^ 2).factorization 5))
    (h5pos : 0 < (m ^ 2).factorization 5) :
    6 ≤ (m ^ 2).factorization 5 := by
  by_contra hnot
  have hsmall : (m ^ 2).factorization 5 ≤ 5 := by omega
  rcases h5even with ⟨u, hu⟩
  have hcases : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 := by omega
  rcases hcases with h2 | h4
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h2
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime (by omega) h5mem h4
