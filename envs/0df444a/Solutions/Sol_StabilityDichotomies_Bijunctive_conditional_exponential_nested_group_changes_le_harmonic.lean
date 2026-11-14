-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_exponential_nested_group_changes_le_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:21.616196+00:00
-- url     : https://prove2.me/submissions/74b1392d-b816-40b1-887a-7bd01b4ca260

import Theorems.Thm_StabilityDichotomies_Bijunctive_selected_conditional_exponential_excesses_are_independent
import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_nested_group_change_probabilities_le_harmonic
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

private def groupEvent {α κ : Type} (T S : Finset α) (label : α → κ) : Set (α → ℝ) :=
  {δ | ∃ a ∈ T, ∃ b ∈ S, (∀ j ∈ T, j ≠ a → δ j < δ a) ∧
    (∀ j ∈ S, δ j ≤ δ b) ∧ label a ≠ label b}
private theorem groupEvent_measurable {α κ : Type} [Fintype α] (T S : Finset α) (label : α → κ) :
    MeasurableSet (groupEvent T S label) := by
  classical
  simp only [groupEvent,setOf_exists,setOf_and,setOf_forall]
  apply MeasurableSet.iUnion; intro a
  apply MeasurableSet.inter (by by_cases h : a ∈ T <;> simp [h])
  apply MeasurableSet.iUnion; intro b
  apply MeasurableSet.inter (by by_cases h : b ∈ S <;> simp [h])
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hj
    apply MeasurableSet.iInter; intro hne
    exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply a)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hj
    exact measurableSet_le (measurable_pi_apply j) (measurable_pi_apply b)
  · apply MeasurableSet.iInter; intro h
    exact MeasurableSet.empty

theorem solution
    {α κ : Type} [Fintype α] (S : Finset α) (β : ℝ) (hβ : 0 < β)
    (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i))
    (sets : ℕ → Finset ↥S) (k : ℕ) (hsub : ∀ i < k, sets (i+1) ⊆ sets i)
    (label : ↥S → κ) :
    let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
    (∑ i ∈ Finset.range k, (μ
      {x : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
        (∀ j ∈ sets i, j ≠ a → x j - d j < x a - d a) ∧
        (∀ j ∈ sets (i+1), x j - d j ≤ x b - d b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  classical
  let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
  let excess : (α → ℝ) → (↥S → ℝ) := fun x i => x i - d i
  have hexcess : Measurable excess := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).sub_const _
  have hmap : μ.map excess = Measure.pi (fun _ : ↥S => expMeasure β) :=
    selected_conditional_exponential_excesses_are_independent S β hβ d s hs hpos hd hselected
  have hstep (i : ℕ) : (μ
      {x : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
        (∀ j ∈ sets i, j ≠ a → x j - d j < x a - d a) ∧
        (∀ j ∈ sets (i+1), x j - d j ≤ x b - d b) ∧ label a ≠ label b}).toReal =
      ((Measure.pi (fun _ : ↥S => expMeasure β)) (groupEvent (sets i) (sets (i+1)) label)).toReal := by
    have h := Measure.map_apply (μ := μ) hexcess (groupEvent_measurable (sets i) (sets (i+1)) label)
    rw [hmap] at h
    exact congrArg ENNReal.toReal h.symm
  have hbase := iid_exponential_nested_group_change_probabilities_le_harmonic sets k hsub label β hβ
  apply le_trans ?_ hbase
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact hstep i
