-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:54:47.770051+00:00
-- url     : https://prove2.me/submissions/7214cb7a-3a1b-4659-b7cf-38acfcc2e03c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_1093_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_support_abundance_absurd

theorem solution (p m d q4 sigma a b c e D : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6)
    (hsigma_p : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (hsigma_eq_p : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i)
    (hfac_q : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma_q : sigma = (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel_q : D * sigma = p * m ^ 2)
    (hDcases_q : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp_q : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  rcases OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_1093_role
      p m d q4 hp hm hpm hprod hsig hsupport h3mem h3exp with hp1093 | hq1093
  · have hprod547 : m ^ 2 = 547 * d := by
      calc
        m ^ 2 = ((p + 1) / 2) * d := hprod
        _ = 547 * d := by rw [hp1093]
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
      m d sigma a b c e hprod547 hsigma_eq_p hpow hsigma_p h3 h19 h547
  · exact OddPerfectNumber.q2_five_q3_nineteen_q4_1093_support_abundance_absurd
      m b c e D p sigma hfac_q hsigma_q hrel_q hDcases_q hp_q hb hc he
