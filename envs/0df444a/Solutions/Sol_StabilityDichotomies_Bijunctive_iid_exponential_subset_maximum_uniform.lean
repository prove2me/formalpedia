-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_exponential_subset_maximum_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:47.768206+00:00
-- url     : https://prove2.me/submissions/90f39639-01c3-474b-b370-840272e49a19

import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_unique_maximum_uniform
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_product_restriction
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

private theorem winner_measurable {n : ℕ} (i : Fin n) :
    MeasurableSet {δ : Fin n → ℝ | ∀ j, j ≠ i → δ j < δ i} := by
  simp only [setOf_forall]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro h
  exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

theorem solution {α : Type} [Fintype α]
    (S : Finset α) (i : α) (hi : i ∈ S) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : α => expMeasure β)
      {δ : α → ℝ | ∀ j ∈ S, j ≠ i → δ j < δ i}).toReal = 1 / S.card := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let e : ↥S ≃ Fin (Fintype.card ↥S) := Fintype.equivFin ↥S
  let i' : ↥S := ⟨i,hi⟩
  let proj : (α → ℝ) → (↥S → ℝ) := fun x k => x k
  have hp : MeasurePreserving proj (Measure.pi (fun _ : α => expMeasure β))
      (Measure.pi (fun _ : ↥S => expMeasure β)) :=
    finite_independent_product_restriction S (fun _ => expMeasure β)
  have he := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ↥S) => expMeasure β) e
  have hmp := he.comp hp
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ↥S) => ℝ) e ∘ proj) ⁻¹'
      {δ : Fin (Fintype.card ↥S) → ℝ | ∀ j, j ≠ e i' → δ j < δ (e i')} =
      {δ : α → ℝ | ∀ j ∈ S, j ≠ i → δ j < δ i} := by
    ext δ
    simp only [mem_preimage,Function.comp_apply,mem_setOf_eq,MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply,eq_rec_constant]
    constructor
    · intro h j hj hji
      have hne : e ⟨j,hj⟩ ≠ e i' := by
        intro hh
        have hx := e.injective hh
        exact hji (congrArg Subtype.val hx)
      have hh := h (e ⟨j,hj⟩) hne
      simpa [proj,i'] using hh
    · intro h k hk
      have hne : (e.symm k).val ≠ i := by
        intro hh
        have hx : e.symm k = i' := Subtype.ext hh
        apply hk
        simpa using congrArg e hx
      have hh := h (e.symm k).val (e.symm k).property hne
      simpa [proj,i'] using hh
  have hh := hmp.measure_preimage (winner_measurable (e i')).nullMeasurableSet
  rw [hpre] at hh
  have hu := iid_exponential_unique_maximum_uniform (Fintype.card ↥S) β hβ (e i')
  rw [← hh] at hu
  simpa [Fintype.card_coe] using hu
