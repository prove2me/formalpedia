-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_ge_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:16:47.649144+00:00
-- url     : https://prove2.me/submissions/ed82290f-a1fc-4dfb-98a3-27457131adf6

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_absurd_v3

theorem solution (p m d q4 sigma a b c e D : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = a)
    (h3pos : 0 < a) (h3even : Even a)
    (hsigma_p : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (hsigma_eq_p : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i)
    (hfac_q : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma_q : sigma =
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel_q : D * sigma = p * m ^ 2)
    (hDcases_q : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp_q : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    8 ≤ a := by
  by_contra hnot
  have halt : a < 8 := by omega
  rcases h3even with ⟨k, hk⟩
  have hcases : a = 2 ∨ a = 4 ∨ a = 6 := by omega
  rcases hcases with h2 | h46
  · have h3exp2 : (m ^ 2).factorization 3 = 2 := by omega
    exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_absurd
      p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h3mem h3exp2)
  · rcases h46 with h4 | h6
    · have h3exp4 : (m ^ 2).factorization 3 = 4 := by omega
      exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_four_absurd
        p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h3mem h3exp4)
    · have h3exp6 : (m ^ 2).factorization 3 = 6 := by omega
      exact False.elim (OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_absurd_v3
        p m d q4 sigma a b c e D hp hm hpm hprod hsig hsupport h3mem h3exp6
        hsigma_p hsigma_eq_p hpow h3 h19 h547 hfac_q hsigma_q hrel_q hDcases_q hp_q hb hc he)
