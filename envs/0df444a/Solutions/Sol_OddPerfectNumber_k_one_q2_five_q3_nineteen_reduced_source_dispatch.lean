-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_reduced_source_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T21:14:20.631124+00:00
-- url     : https://prove2.me/submissions/6200a4df-017b-4edc-af13-1a40edff0ded

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_source_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

theorem solution (sigma a b c e q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcase :
      ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨
        (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma)) ∨
      (q4 = 101 ∧ 1709 ∣ sigma ∧
        Even (orderOf (3 : ZMod 1709)) ∧ Even (orderOf (5 : ZMod 1709)) ∧
        Even (orderOf (19 : ZMod 1709)) ∧ Even (orderOf (101 : ZMod 1709))) ∨
      (q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  rcases hcase with h57 | h101 | h135
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e q4 hsigma h57
  · rcases h101 with ⟨rfl, hdiv, h3, h5, h19, h101⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_source_absurd
      sigma a b c e hsigma hdiv h3 h5 h19 h101
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_absurd
      q4 h135.1 h135.2.1 h135.2.2
