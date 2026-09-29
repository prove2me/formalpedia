-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:26:14.219512+00:00
-- url     : https://prove2.me/submissions/9f5db2b9-1998-4f45-b047-34947ff28614

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (hq4ne : q4 ≠ 127) :
    4 ≤ (m ^ 2).factorization 19 := by
  by_contra hnot
  rcases h19even with ⟨k, hk⟩
  have htwo : (m ^ 2).factorization 19 = 2 := by
    omega
  exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd
    p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h19mem htwo hq4ne)
