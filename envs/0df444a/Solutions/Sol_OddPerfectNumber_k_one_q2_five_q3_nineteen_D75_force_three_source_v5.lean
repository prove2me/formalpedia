-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source_v5
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:30.085986+00:00
-- url     : https://prove2.me/submissions/b17f5e53-cc31-4cc1-8b65-cc133f5a992f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_force_three_source_v9

open OddPerfectNumber

theorem solution (sigma a b c e : Nat)
  (hsigma : sigma =
   (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
   (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
   (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
   (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
  (hdiv : 263 ∣ sigma) :
    130 ≤ 2 * a :=
  OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source_v9 sigma a b c e hsigma hdiv
