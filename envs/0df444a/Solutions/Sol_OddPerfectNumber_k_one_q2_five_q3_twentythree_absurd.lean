-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:02:07.664722+00:00
-- url     : https://prove2.me/submissions/b313253e-b551-4659-8076-ba40876e0ff9

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_53_no_five_source

theorem solution (sigma a b c e q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hfinite :
      (((q4 = 691 ∨ q4 = 701 ∨ q4 = 709) ∧ 53 ∣ sigma) ∨
        (q4 = 53 ∧ 5 ∣ sigma))) :
    False := by
  rcases hfinite with hsmall | hlarge
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_absurd
      sigma a b c e q4 hsigma hsmall.2 hsmall.1
  · rcases hlarge with ⟨hq4, hdiv⟩
    subst q4
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_53_no_five_source
      sigma a b c e hsigma hdiv
