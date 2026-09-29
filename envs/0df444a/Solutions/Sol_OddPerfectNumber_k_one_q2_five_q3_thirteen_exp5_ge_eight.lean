-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp5_ge_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:11:56.64393+00:00
-- url     : https://prove2.me/submissions/802aacc0-32ba-416f-858b-db6e7703d3f5

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_small_exponents_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5) (h5even : Even ((m ^ 2).factorization 5)) :
    8 ≤ (m ^ 2).factorization 5 := by
  by_contra hlt
  rcases h5even with ⟨k, hk⟩
  have hcases : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 ∨
      (m ^ 2).factorization 5 = 6 := by
    omega
  exact OddPerfectNumber.k_one_q2_five_q3_thirteen_small_exponents_absurd
    p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem hcases
