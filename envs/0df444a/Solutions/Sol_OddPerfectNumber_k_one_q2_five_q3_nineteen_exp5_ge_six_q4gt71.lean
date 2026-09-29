-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:15:11.386348+00:00
-- url     : https://prove2.me/submissions/d7589a26-2316-43ba-b3dd-b24928232b38

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 71 < q4)
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
  · have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
      p m d q4 hp hm hpm hprod hsig hsupport hq4prime (by omega) h5mem h2
    rcases hrole with hp31 | hq431
    · subst p
      norm_num at hp4
    · omega
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71
      p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h5mem h4
