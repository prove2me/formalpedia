-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P84.optical_cut_factor_two
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:35:16.537429+00:00
-- url     : https://prove2.me/submissions/0428519a-0003-40b4-bb74-37b5f264eea4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P84

noncomputable section

open QAlgorithms

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intakenext100.P84 in
theorem solution {E : Type*} [Fintype E]
    (frequency eta : E → ℝ)
    (hfrequency : ∀ e, 0 ≤ frequency e)
    (heta : ∀ e, 0 ≤ eta e ∧ eta e < 1) :
    (∑ e, frequency e * Real.logb 2 ((1 + eta e) / (1 - eta e))) ≤
      2 * ∑ e, frequency e * Real.logb 2 (1 / (1 - eta e)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  obtain ⟨h0, h1⟩ := heta e
  have hpos : 0 < 1 - eta e := by linarith
  have hne : (1 / (1 - eta e)) ≠ 0 := by positivity
  have key : Real.logb 2 ((1 + eta e) / (1 - eta e)) ≤ 2 * Real.logb 2 (1 / (1 - eta e)) := by
    rw [two_mul, ← Real.logb_mul hne hne]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [div_le_iff₀ hpos]
    field_simp
    nlinarith
  have := mul_le_mul_of_nonneg_left key (hfrequency e)
  linarith
