-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_excluded_priority_vector_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:27:33.307926+00:00
-- url     : https://prove2.me/submissions/6add9ec1-bd8a-477e-8cdc-1fc8e694daf7

import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_first_mask_priority_law
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

private theorem included_priority_probability (ε : ℝ) (hε0 : 0 ≤ ε) :
    unitPriorityMeasure (Iic (1 - ε / 2)) = ENNReal.ofReal (1 - ε / 2) := by
  unfold unitPriorityMeasure
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have he : Icc (0 : ℝ) 1 ∩ Iic (1 - ε / 2) = Icc 0 (1 - ε / 2) := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · rintro ⟨⟨h0,h1⟩,h⟩; exact ⟨h0,h⟩
    · rintro ⟨h0,h⟩; exact ⟨⟨h0,by linarith⟩,h⟩
  rw [he,Real.volume_Icc,Real.volume_Icc]
  norm_num

theorem solution {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    Measure.map (fun x : α → ℝ => fun i : {i // m i = false} => x i)
      (ProbabilityTheory.cond (Measure.pi (fun _ : α => unitPriorityMeasure))
        (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))) =
    Measure.pi (fun _ : {i // m i = false} => cutoffMeasure ε) := by
  classical
  rw [conditional_first_mask_priority_law ε hε hε1 m]
  let ν : α → Measure ℝ := fun i => if m i then ProbabilityTheory.cond unitPriorityMeasure (Iic (1 - ε / 2)) else cutoffMeasure ε
  haveI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI (i : α) : IsProbabilityMeasure (ν i) := by
    dsimp [ν]
    split
    · apply cond_isProbabilityMeasure_of_finite
      · rw [included_priority_probability ε (le_of_lt hε)]
        exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
      · exact measure_ne_top _ _
    · infer_instance
  let p : α → Prop := fun i => m i = false
  have h := (measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd ν p)).map_eq
  have hh : (fun x : α → ℝ => fun i : {i // m i = false} => x i) =
      Prod.fst ∘ MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ) p := by
    funext x i
    rfl
  rw [hh]
  rw [h]
  congr 1
  funext i
  have hi : m i = false := i.property
  simp [ν,hi]
