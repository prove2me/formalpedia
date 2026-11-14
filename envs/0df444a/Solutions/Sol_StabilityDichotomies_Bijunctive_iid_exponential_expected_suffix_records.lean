-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_exponential_expected_suffix_records
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:48.968568+00:00
-- url     : https://prove2.me/submissions/72b905b8-3b28-407c-bbe9-5ec131a8216f

import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_subset_maximum_uniform
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

private def recordEvent (n : ℕ) (i : Fin n) : Set (Fin n → ℝ) :=
  {δ | ∀ j ∈ Finset.Ici i, j ≠ i → δ j < δ i}
private theorem record_measurable (n : ℕ) (i : Fin n) : MeasurableSet (recordEvent n i) := by
  unfold recordEvent
  simp only [setOf_forall]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro hj
  apply MeasurableSet.iInter; intro hne
  exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

private theorem reverse_reciprocal_sum_eq_harmonic (n : ℕ) :
    (∑ i : Fin n, (1 : ℝ) / (n - i.val)) = (harmonic n : ℝ) := by
  change (∑ i : Fin n, (fun k : ℕ => (1 : ℝ) / (n - k)) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 : ℝ) / (n - k)) n]
  have hrev := Finset.sum_range_reflect (fun k : ℕ => (1 : ℝ) / ((k+1 : ℕ) : ℝ)) n
  calc
    _ = ∑ j ∈ Finset.range n, (1 : ℝ) / ((n - 1 - j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have he : n - 1 - j + 1 = n - j := by omega
      rw [he,Nat.cast_sub (Nat.le_of_lt hjn)]
    _ = ∑ j ∈ Finset.range n, (1 : ℝ) / ((j+1 : ℕ) : ℝ) := hrev
    _ = (harmonic n : ℝ) := by
      simp [harmonic,div_eq_mul_inv]

theorem solution (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : Fin n => expMeasure β)
    let R := fun δ : Fin n → ℝ => ∑ i : Fin n,
      if ∀ j ∈ Finset.Ici i, j ≠ i → δ j < δ i then (1 : ℝ) else 0
    Integrable R μ ∧ (∫ δ, R δ ∂μ) = (harmonic n : ℝ) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  let g : Fin n → (Fin n → ℝ) → ℝ := fun i δ => if δ ∈ recordEvent n i then 1 else 0
  have hg (i : Fin n) : Integrable (g i) μ := by
    have he : g i = (recordEvent n i).indicator (fun _ => (1 : ℝ)) := by
      funext δ
      by_cases h : δ ∈ recordEvent n i <;> simp [g,Set.indicator_apply,h]
    rw [he]
    exact (integrable_const (μ := μ) (1 : ℝ)).indicator (record_measurable n i)
  have hint : Integrable (fun δ => ∑ i, g i δ) μ := integrable_finsetSum _ (fun i _ => hg i)
  rw [← reverse_reciprocal_sum_eq_harmonic n]
  dsimp only
  have hR : (fun δ : Fin n → ℝ => ∑ i : Fin n,
      if ∀ j ∈ Finset.Ici i, j ≠ i → δ j < δ i then (1 : ℝ) else 0) =
      (fun δ => ∑ i, g i δ) := by
    funext δ
    apply Finset.sum_congr rfl
    intro i _
    simp only [g,recordEvent,mem_setOf_eq]
  rw [hR]
  change Integrable (fun δ => ∑ i, g i δ) μ ∧
    (∫ δ, ∑ i, g i δ ∂μ) = ∑ i : Fin n, (1 : ℝ) / (n - i.val)
  refine ⟨hint,?_⟩
  rw [integral_finsetSum _ (fun i _ => hg i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := iid_exponential_subset_maximum_uniform (Finset.Ici i) i (Finset.mem_Ici.mpr le_rfl) β hβ
  have hintg : (∫ δ, g i δ ∂μ) = μ.real (recordEvent n i) := by
    have he : g i = (recordEvent n i).indicator (fun _ => (1 : ℝ)) := by
      funext δ
      by_cases h : δ ∈ recordEvent n i <;> simp [g,Set.indicator_apply,h]
    rw [he]
    exact integral_indicator_one (μ := μ) (record_measurable n i)
  rw [hintg]
  change ((Measure.pi (fun _ : Fin n => expMeasure β))
    {δ : Fin n → ℝ | ∀ j ∈ Finset.Ici i, j ≠ i → δ j < δ i}).toReal = _
  simpa [Fin.card_Ici] using hp
