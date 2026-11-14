-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_exponential_nested_group_change_probabilities_le_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:52.86203+00:00
-- url     : https://prove2.me/submissions/4de2d96e-f04e-45c3-9414-3bf8ec4367e6

import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_group_removal_change_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_grouped_removal_fraction_sum_le_harmonic
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

theorem solution
    {α κ : Type} [Fintype α] (sets : ℕ → Finset α) (k : ℕ)
    (hsub : ∀ i < k, sets (i+1) ⊆ sets i) (label : α → κ) (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : α => expMeasure β)
        {δ : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
          (∀ j ∈ sets i, j ≠ a → δ j < δ a) ∧
          (∀ j ∈ sets (i+1), δ j ≤ δ b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  classical
  let m : ℕ → ℕ := fun i => (sets i).card
  have hmono : ∀ i < k, m (i+1) ≤ m i := by
    intro i hi
    exact Finset.card_le_card (hsub i hi)
  calc
    _ ≤ ∑ i ∈ Finset.range k, ((m i - m (i+1) : ℕ) : ℝ) / m i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := iid_exponential_group_removal_change_bound (sets i) (sets (i+1))
        (hsub i (Finset.mem_range.mp hi)) label β hβ
      have hc : ((sets i \ sets (i+1)).card : ℕ) = m i - m (i+1) := by
        have hh := Finset.card_sdiff_add_card_eq_card (hsub i (Finset.mem_range.mp hi))
        dsimp [m]
        omega
      simpa [m,hc] using h
    _ ≤ (harmonic (m 0) : ℝ) := grouped_removal_fraction_sum_le_harmonic k m hmono
