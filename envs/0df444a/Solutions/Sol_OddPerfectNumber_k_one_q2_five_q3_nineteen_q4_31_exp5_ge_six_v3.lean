-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:21:34.292665+00:00
-- url     : https://prove2.me/submissions/2ec055ae-4ed4-4626-9de4-806ae73b2361

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

theorem solution (p m d sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hsupport_m : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = 31)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31))
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5)) :
    6 ≤ (m ^ 2).factorization 5 := by
  by_contra hnot
  rcases h5even with ⟨k, hk⟩
  have hcases : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 := by
    omega
  rcases hcases with h2 | h4
  · have hsigma2 := hsigma
    rw [h2] at hsigma2
    exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd_v2
      p m d sigma hp hp4 hm hpm hprod hsig hsupport hupper hsigma2
      h3mem h3pos h3even h19pos h19even h31pos h31even h2)
  · have hq4prime : (31 : Nat).Prime := by norm_num
    have hq4gt : 19 < (31 : Nat) := by norm_num
    exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd
      p m d 31 hp hp4 hm hpm hprod hsig hsupport_m hq4prime hq4gt h5mem h4)
