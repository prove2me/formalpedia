-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_cases_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T23:04:21.452017+00:00
-- url     : https://prove2.me/submissions/a0e0a4b7-6dcd-41a6-b504-aad804b1366c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_41_absurd

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1)
    (hq4cases : q4 = 31 ∨ q4 = 41)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  rcases hq4cases with h31 | h41
  · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
      m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq h31 ha hb hc he
  · have haE : Even (2*a) := ⟨a, by omega⟩
    have hbE : Even (2*b) := ⟨b, by omega⟩
    have hcE : Even (2*c) := ⟨c, by omega⟩
    have heE : Even (2*e) := ⟨e, by omega⟩
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_41_absurd
      m a b c e D p q4 sigma hsigma hrel hD hp_eq h41 haE hbE hcE heE
