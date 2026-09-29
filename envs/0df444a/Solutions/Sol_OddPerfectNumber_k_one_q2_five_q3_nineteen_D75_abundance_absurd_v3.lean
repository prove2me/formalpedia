-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_abundance_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:28.650578+00:00
-- url     : https://prove2.me/submissions/3126879c-9fd7-4a65-83f6-179640115dda

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v4

open OddPerfectNumber

theorem solution (m a b c e sigma : Nat)
  (hfac : m ^ 2 = 3 ^ (2 * a) * 5 ^ (2 * b) * 19 ^ (2 * c) * 263 ^ (2 * e))
  (hsigma : sigma =
   (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
   (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
   (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
   (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
  (hrel : 75 * sigma = 149 * m ^ 2)
  (hdiv : 263 ∣ sigma)
  (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_abundance_absurd_v4 m a b c e sigma hfac hsigma hrel hdiv hb hc he
