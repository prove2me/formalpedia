-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:09:42.768375+00:00
-- url     : https://prove2.me/submissions/4eacf47c-9c93-4804-a4a3-322ea0699930

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (hq4ne : q4 ≠ 31) :
    6 ≤ (m ^ 2).factorization 5 := by
  by_contra hnot
  rcases h5even with ⟨k, hk⟩
  have hcases : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 := by
    omega
  rcases hcases with h2 | h4
  · have hroles := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
      p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h2
    rcases hroles with hp31 | hq431
    · exact OddPerfectNumber.k_one_p31_hprod_odd_square_absurd p m d hm hprod hp31
    · exact hq4ne hq431
  · exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h4)
