-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.selected_conditional_exponential_excesses_are_independent
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:45.445196+00:00
-- url     : https://prove2.me/submissions/925d44ca-7371-4915-b341-7b6984699bc6

import Theorems.Thm_StabilityDichotomies_Bijunctive_condition_finite_product_on_rectangle
import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_shifted_exponential_law
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_product_restriction
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

theorem solution
    {α : Type} [Fintype α] (S : Finset α) (β : ℝ) (hβ : 0 < β)
    (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i)) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)).map
      (fun x : α → ℝ => fun i : ↥S => x i - d i) =
      Measure.pi (fun _ : ↥S => expMeasure β) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let ν : α → Measure ℝ := fun i => ProbabilityTheory.cond (expMeasure β) (s i)
  haveI (i : α) : IsProbabilityMeasure (ν i) :=
    cond_isProbabilityMeasure_of_finite (hpos i) (measure_ne_top (expMeasure β) (s i))
  have hrect : ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s) =
      Measure.pi ν := condition_finite_product_on_rectangle (fun _ => expMeasure β) s hs hpos
  rw [hrect]
  let proj : (α → ℝ) → (↥S → ℝ) := fun x i => x i
  let shift : (↥S → ℝ) → (↥S → ℝ) := fun x i => x i - d i
  have hp : MeasurePreserving proj (Measure.pi ν) (Measure.pi (fun i : ↥S => ν i)) :=
    finite_independent_product_restriction S ν
  have hm : Measurable shift := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).sub_const _
  have hlaw (i : ↥S) : (ν i).map (fun x : ℝ => x - d i) = expMeasure β := by
    dsimp [ν]
    rw [hselected i i.2]
    exact conditional_shifted_exponential_law β (d i) hβ (hd i i.2)
  haveI (i : ↥S) : IsProbabilityMeasure ((ν i).map (fun x : ℝ => x - d i)) := by
    rw [hlaw i]
    infer_instance
  change (Measure.pi ν).map (shift ∘ proj) = _
  rw [← Measure.map_map hm hp.measurable, hp.map_eq]
  have hh := Measure.pi_map_pi (μ := fun i : ↥S => ν i) (f := fun i (x : ℝ) => x-d i)
    (fun i => (measurable_id.sub_const (d i)).aemeasurable)
  change (Measure.pi (fun i : ↥S => ν i)).map shift = _ at hh
  rw [hh]
  congr 1
  funext i
  exact hlaw i
