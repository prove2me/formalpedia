-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_iid_fin_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:34:04.038718+00:00
-- url     : https://prove2.me/submissions/111493d7-4c88-414f-b3f3-8314215d9cd9

import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_priorities_and_cutoff_joint_law
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem solution {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool)
    (n : ℕ) (e : Fin n ≃ Option {i // m i = false}) :
    Measure.map ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) ∘
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // m i = false} => ℝ)).symm ∘
      (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2)))
      (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)) =
    Measure.pi (fun _ : Fin n => cutoffMeasure ε) := by
  classical
  let D := {i // m i = false}
  let Q := ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)
  let proj : ((α → ℝ) × ℝ) → ((D → ℝ) × ℝ) := fun z => (fun i => z.1 i,z.2)
  let opt := (MeasurableEquiv.piOptionEquivProd (fun _ : Option D => ℝ)).symm
  let fin := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  haveI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hp : Measurable proj := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply (i : α)).comp measurable_fst
    · exact measurable_snd
  have hm : Measure.map proj Q = (Measure.pi (fun _ : D => cutoffMeasure ε)).prod (cutoffMeasure ε) :=
    conditional_excluded_priorities_and_cutoff_joint_law ε hε hε1 m
  have hopt : Measure.map opt ((Measure.pi (fun _ : D => cutoffMeasure ε)).prod (cutoffMeasure ε)) =
      Measure.pi (fun _ : Option D => cutoffMeasure ε) := Measure.pi_map_piOptionEquivProd (fun _ => cutoffMeasure ε)
  have hfin := (measurePreserving_piCongrLeft (fun _ : Fin n => cutoffMeasure ε) e.symm).map_eq
  change Measure.map (fin ∘ (opt ∘ proj)) Q = _
  rw [← Measure.map_map fin.measurable (opt.measurable.comp hp), ← Measure.map_map opt.measurable hp, hm, hopt]
  exact hfin
