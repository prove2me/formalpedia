-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:31:59.289236+00:00
-- url     : https://prove2.me/submissions/2f183046-462b-4023-a661-e77ffebea8d9

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_587_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_593_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd

theorem solution (sigma a b c e q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcase :
      (q4 = 587 ∧ 113 ∣ sigma) ∨
      (q4 = 593 ∧ 593 ∣ sigma) ∨
      (q4 = 599 ∧ 113 ∣ sigma) ∨
      (q4 = 601 ∧ 113 ∣ sigma)) :
    False := by
  rcases hcase with h587 | h593 | h599 | h601
  · rcases h587 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_587_absurd
      sigma a b c e hsigma hdiv
  · rcases h593 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_593_absurd
      sigma a b c e hsigma hdiv
  · rcases h599 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd
      sigma a b c e 599 hsigma (Or.inl ⟨rfl, hdiv⟩)
  · rcases h601 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd
      sigma a b c e 601 hsigma (Or.inr ⟨rfl, hdiv⟩)
