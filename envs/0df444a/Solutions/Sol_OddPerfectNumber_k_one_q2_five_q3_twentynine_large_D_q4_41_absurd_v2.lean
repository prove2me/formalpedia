-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:17.933638+00:00
-- url     : https://prove2.me/submissions/495ca537-6c15-45c9-a1dc-ce036f4b0ff6

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hDupper : D ≤ 105) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4eq : q4 = 41) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3 m a b c e D p q4 sigma hfac hsigma hrel hDlow hDupper hDodd hp hp_eq hq4eq hDsupport ha hb hc he
