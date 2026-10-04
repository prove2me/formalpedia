-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T15:48:29.282037+00:00
-- url     : https://prove2.me/submissions/e6187dc5-e51d-4028-ad13-a42e9ccaadd8

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
       (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma))) ∨
      (D = 75 ∧ q4 = 263 ∧
      (∃ m a' b' c' e',
        m ^ 2 = 3 ^ (2 * a') * 5 ^ (2 * b') * 19 ^ (2 * c') * 263 ^ (2 * e') ∧
        sigma = (∑ i ∈ Finset.range (2 * a' + 1), 3 ^ i) *
          (∑ i ∈ Finset.range (2 * b' + 1), 5 ^ i) *
          (∑ i ∈ Finset.range (2 * c' + 1), 19 ^ i) *
          (∑ i ∈ Finset.range (2 * e' + 1), 263 ^ i) ∧
        75 * sigma = 149 * m ^ 2 ∧ 263 ∣ sigma ∧
        3 ≤ b' ∧ 2 ≤ c' ∧ 1 ≤ e')) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  have hcases_v3 : (D = 57 ∧
      ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨
       (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma))) ∨
      (D = 75 ∧ q4 = 263 ∧
      (∃ m a' b' c' e',
        m ^ 2 = 3 ^ (2 * a') * 5 ^ (2 * b') * 19 ^ (2 * c') * 263 ^ (2 * e') ∧
        sigma = (∑ i ∈ Finset.range (2 * a' + 1), 3 ^ i) *
          (∑ i ∈ Finset.range (2 * b' + 1), 5 ^ i) *
          (∑ i ∈ Finset.range (2 * c' + 1), 19 ^ i) *
          (∑ i ∈ Finset.range (2 * e' + 1), 263 ^ i) ∧
        75 * sigma = 149 * m ^ 2 ∧ 3 ≤ b' ∧ 2 ≤ c' ∧ 1 ≤ e')) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148) := by
    rcases hcases with h57 | h75 | h135
    · exact Or.inl h57
    · rcases h75 with ⟨hD, hq4, hm⟩
      rcases hm with
        ⟨m, a', b', c', e', hfac, hsigma', hrel, _h263, hb, hc, he⟩
      exact Or.inr (Or.inl ⟨hD, hq4,
        ⟨m, a', b', c', e', hfac, hsigma', hrel, hb, hc, he⟩⟩)
    · exact Or.inr (Or.inr h135)
  rcases hcases_v3 with h57 | h75 | h135
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
