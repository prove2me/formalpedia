-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_685_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:15.012348+00:00
-- url     : https://prove2.me/submissions/4013f328-8ed0-47a6-95f2-a01e58a9171e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_685_v5

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D) (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt47 : 47 < q4) (hq4le : q4 ≤ 61) (hq4dvd : q4 ∣ D) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    D ≤ 685 :=
  OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_685_v5 m a b c e D p q4 sigma hfac hsigma hrel hDlow hDodd hp hp4 hp_eq hq4prime hq4gt47 hq4le hq4dvd hDsupport ha hb hc he
