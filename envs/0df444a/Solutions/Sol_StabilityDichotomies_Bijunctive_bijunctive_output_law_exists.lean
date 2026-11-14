-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_output_law_exists
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:50.373464+00:00
-- url     : https://prove2.me/submissions/a297f8b9-c093-4871-8df8-b1103646010e

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
noncomputable section
open scoped Classical
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (ε : ℝ) (hε : 0 < ε) : ∃ A : Solver Γ, BijunctiveOutputLaw Γ rep ε A := by
  let A : Solver Γ := fun V _ I =>
    let μ := bijunctiveSeedMeasure rep I ε
    let f := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2
    have hf : Measurable f := by
      apply measurable_to_countable
      intro s
      exact bijunctive_output_event_measurable rep I ε (f s)
    haveI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
    haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
    (μ.map f).toPMF
  refine ⟨A, ?_⟩
  intro V _ I hSat x
  have hf : Measurable (fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2) := by
    apply measurable_to_countable
    intro s
    exact bijunctive_output_event_measurable rep I ε (bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)
  haveI : IsProbabilityMeasure (bijunctiveSeedMeasure rep I ε) := bijunctive_seed_is_probability rep I ε hε
  haveI : IsProbabilityMeasure ((bijunctiveSeedMeasure rep I ε).map (fun s :
      (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) => bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  change (((bijunctiveSeedMeasure rep I ε).map (fun s :
    (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
    bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)).toPMF x).toReal = _
  rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton x)]
  rfl
