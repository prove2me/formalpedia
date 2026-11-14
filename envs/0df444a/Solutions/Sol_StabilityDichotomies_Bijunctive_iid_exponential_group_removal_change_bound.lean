-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_exponential_group_removal_change_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:49.300494+00:00
-- url     : https://prove2.me/submissions/2f80d8a8-cffc-4903-8290-a283b01d335a

import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_subset_maximum_uniform
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

theorem solution {α κ : Type} [Fintype α]
    (T S : Finset α) (hsub : S ⊆ T) (label : α → κ) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : α => expMeasure β)
      {δ : α → ℝ | ∃ a ∈ T, ∃ b ∈ S,
        (∀ j ∈ T, j ≠ a → δ j < δ a) ∧
        (∀ j ∈ S, δ j ≤ δ b) ∧ label a ≠ label b}).toReal ≤
      ((T \ S).card : ℝ) / T.card := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  let W : α → Set (α → ℝ) := fun a => {δ | ∀ j ∈ T, j ≠ a → δ j < δ a}
  let E : Set (α → ℝ) := {δ | ∃ a ∈ T, ∃ b ∈ S,
        (∀ j ∈ T, j ≠ a → δ j < δ a) ∧
        (∀ j ∈ S, δ j ≤ δ b) ∧ label a ≠ label b}
  have hcover : E ⊆ ⋃ a ∈ T \ S, W a := by
    intro δ hδ
    obtain ⟨a,ha,b,hb,hmaxa,hmaxb,hlabel⟩ := hδ
    have hanS : a ∉ S := by
      intro has
      have hne : b ≠ a := by intro he; subst b; exact hlabel rfl
      have hbT := hsub hb
      have hba := hmaxa b hbT hne
      have hab := hmaxb a has
      exact (not_lt_of_ge hab) hba
    apply Set.mem_iUnion.mpr
    refine ⟨a,Set.mem_iUnion.mpr ⟨Finset.mem_sdiff.mpr ⟨ha,hanS⟩,hmaxa⟩⟩
  calc
    μ.real E ≤ μ.real (⋃ a ∈ T \ S, W a) := measureReal_mono hcover (measure_ne_top μ _)
    _ ≤ ∑ a ∈ T \ S, μ.real (W a) := measureReal_biUnion_finset_le _ _
    _ = ∑ _a ∈ T \ S, (1 : ℝ) / T.card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact iid_exponential_subset_maximum_uniform T a (Finset.mem_sdiff.mp ha).1 β hβ
    _ = ((T \ S).card : ℝ) / T.card := by simp [div_eq_mul_inv]
