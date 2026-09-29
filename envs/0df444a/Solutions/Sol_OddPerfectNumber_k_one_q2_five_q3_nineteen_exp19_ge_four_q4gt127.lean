-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4gt127
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:20:57.021344+00:00
-- url     : https://prove2.me/submissions/6ddbcfa7-c460-4d76-93f9-844c3f5fe8c2

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_two_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19even : Even ((m ^ 2).factorization 19))
    (h19pos : 0 < (m ^ 2).factorization 19) :
    4 ≤ (m ^ 2).factorization 19 := by
  by_contra hnot
  have hsmall : (m ^ 2).factorization 19 ≤ 3 := by omega
  rcases h19even with ⟨u, hu⟩
  have htwo : (m ^ 2).factorization 19 = 2 := by omega
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_two_absurd
    p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h19mem htwo
