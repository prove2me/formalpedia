-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_exponential_excess_expected_records
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:35.489318+00:00
-- url     : https://prove2.me/submissions/264cc832-83e3-477d-92f8-ede1ddc686ab

import Theorems.Thm_StabilityDichotomies_Bijunctive_selected_conditional_exponential_excesses_are_independent
import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_expected_suffix_records
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem solution
    {α : Type} [Fintype α] (S : Finset α) (ord : Fin S.card ≃ ↥S)
    (β : ℝ) (hβ : 0 < β) (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i)) :
    let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
    let R := fun x : α → ℝ => ∑ i : Fin S.card,
      if ∀ j ∈ Finset.Ici i, j ≠ i → x (ord j) - d (ord j) < x (ord i) - d (ord i)
      then (1 : ℝ) else 0
    Integrable R μ ∧ (∫ x, R x ∂μ) = (harmonic S.card : ℝ) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
  let μS : Measure (↥S → ℝ) := Measure.pi (fun _ => expMeasure β)
  let μN : Measure (Fin S.card → ℝ) := Measure.pi (fun _ => expMeasure β)
  let excess : (α → ℝ) → (↥S → ℝ) := fun x i => x i - d i
  let reorder : (↥S → ℝ) → (Fin S.card → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin S.card => ℝ) ord.symm
  have hexcess : Measurable excess := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).sub_const _
  have hmap : μ.map excess = μS :=
    selected_conditional_exponential_excesses_are_independent S β hβ d s hs hpos hd hselected
  have hp : MeasurePreserving excess μ μS := ⟨hexcess,hmap⟩
  have hr : MeasurePreserving reorder μS μN :=
    measurePreserving_piCongrLeft (fun _ : Fin S.card => expMeasure β) ord.symm
  have hpr := hr.comp hp
  let R : (Fin S.card → ℝ) → ℝ := fun y => ∑ i : Fin S.card,
    if ∀ j ∈ Finset.Ici i, j ≠ i → y j < y i then 1 else 0
  have hR := iid_exponential_expected_suffix_records S.card β hβ
  have hint : Integrable (R ∘ (reorder ∘ excess)) μ :=
    (hpr.integrable_comp hR.1.aestronglyMeasurable).2 hR.1
  have heq : (∫ x, (R ∘ (reorder ∘ excess)) x ∂μ) = ∫ y, R y ∂μN := by
    have hm : AEStronglyMeasurable R (Measure.map (reorder ∘ excess) μ) := by
      rw [hpr.map_eq]
      exact hR.1.aestronglyMeasurable
    have hh := integral_map hpr.measurable.aemeasurable hm
    rw [hpr.map_eq] at hh
    exact hh.symm
  have hfunc : (R ∘ (reorder ∘ excess)) = (fun x : α → ℝ => ∑ i : Fin S.card,
      if ∀ j ∈ Finset.Ici i, j ≠ i → x (ord j) - d (ord j) < x (ord i) - d (ord i)
      then (1 : ℝ) else 0) := by
    funext x
    simp only [Function.comp_apply,R,reorder,excess,MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply,eq_rec_constant,Equiv.symm_symm]
  rw [hfunc] at hint heq
  exact ⟨hint,heq.trans hR.2⟩
