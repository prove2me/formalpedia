-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_canonical_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T10:23:38.618891+00:00
-- url     : https://prove2.me/submissions/fe6a4a6d-b52b-4090-b098-99fa97a4cbe0

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 41)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  have hDupper := OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v2
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4eq
    ha hb hc he
  exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hDupper hDodd hp hp_eq
    hq4eq hDsupport ha hb hc he
