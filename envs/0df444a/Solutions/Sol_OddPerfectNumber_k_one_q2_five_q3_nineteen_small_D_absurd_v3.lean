-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T01:18:43.838935+00:00
-- url     : https://prove2.me/submissions/9dfedf57-aa96-4b5f-9bfb-b9bb5a648676

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

theorem solution
    (sigma a b c e q4 D : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcases : (D = 57 ∧
      ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨
       (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma)))
      ∨ (D = 75 ∧ q4 = 263 ∧
      (∃ m a' b' c' e',
        m ^ 2 = 3 ^ (2 * a') * 5 ^ (2 * b') * 19 ^ (2 * c') * 263 ^ (2 * e') ∧
        sigma =
          (∑ i ∈ Finset.range (2 * a' + 1), 3 ^ i) *
          (∑ i ∈ Finset.range (2 * b' + 1), 5 ^ i) *
          (∑ i ∈ Finset.range (2 * c' + 1), 19 ^ i) *
          (∑ i ∈ Finset.range (2 * e' + 1), 263 ^ i) ∧
        75 * sigma = 149 * m ^ 2 ∧
        3 ≤ b' ∧ 2 ≤ c' ∧ 1 ≤ e'))
      ∨ (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  rcases hcases with h57 | h75 | h135
  · obtain ⟨_, hcase⟩ := h57
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e q4 hsigma hcase
  · obtain ⟨_, _, hm⟩ := h75
    obtain ⟨m, a', b', c', e', hfac, hsigma', hrel, hb, hc, he⟩ := hm
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
      m a' b' c' e' sigma hfac hsigma' hrel hb hc he
  · obtain ⟨_, hqprime, hlow, hhigh⟩ := h135
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_absurd
      q4 hqprime hlow hhigh
