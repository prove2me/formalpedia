-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_263_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T21:52:18.718893+00:00
-- url     : https://prove2.me/submissions/e7d832a2-0438-41ad-8892-6ed8ff7d71de

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_p149_no_local_sigma_source_general

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 149 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 149) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 149) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 149) ∣ 2 * c + 1)
    (h263 : ¬ orderOf (263 : ZMod 149) ∣ 2 * e + 1) :
    False := by
  exact OddPerfectNumber.k_one_p149_no_local_sigma_source_general
    sigma a b c e 263 hsigma hdiv h3 h5 h19 h263
