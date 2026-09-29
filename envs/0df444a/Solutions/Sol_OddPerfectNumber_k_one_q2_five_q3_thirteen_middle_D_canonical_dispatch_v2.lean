-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_canonical_dispatch_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T02:14:17.851287+00:00
-- url     : https://prove2.me/submissions/2dc85b6a-7448-4f43-974d-646c7a03ae40

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_absurd_v2

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D)
    (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_candidates
    D p q4 hDlow hDhigh hp hp4 hp_eq hq4 hq4gt hq4le hq4dvd
  exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd_v2
    m a b c e D p q4 sigma hfac hsigma hrel hcases hq4 ha hb hc he
