-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_q4_13_absurd
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:32.602301+00:00
-- url     : https://prove2.me/submissions/20b6ddd1-ac7f-4d4a-9ac4-a6faa42b3a7b

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_q4_13_absurd_v2

open OddPerfectNumber

theorem solution (m b c e sigma : Nat)
  (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * 13 ^ e)
  (hsigma : sigma =
   (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
   (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
   (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
   (∑ i ∈ Finset.range (e + 1), 13 ^ i))
  (hupper : sigma ≤ 2 * m ^ 2)
  (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_eleven_q4_13_absurd_v2 m b c e sigma hfac hsigma hupper hb hc he
