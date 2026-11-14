-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_excluded_priorities_and_cutoff_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:32:03.49402+00:00
-- url     : https://prove2.me/submissions/abf89668-96cf-400e-91dc-6cc00c43bf4f

import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_priority_vector_law
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

private theorem condition_product_on_left_event {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν] (s : Set α) :
    ProbabilityTheory.cond (μ.prod ν) (s ×ˢ Set.univ) = (ProbabilityTheory.cond μ s).prod ν := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, mul_one]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [Measure.prod_smul_left]

theorem solution {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    Measure.map (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2))
      (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)) =
    (Measure.pi (fun _ : {i // m i = false} => cutoffMeasure ε)).prod (cutoffMeasure ε) := by
  classical
  let μ := Measure.pi (fun _ : α => unitPriorityMeasure)
  let s : Set (α → ℝ) := Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))
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
  have hcond : ProbabilityTheory.cond μ s = Measure.pi ν := StabilityDichotomies.Bijunctive.conditional_first_mask_priority_law ε hε hε1 m
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ s) := by rw [hcond]; infer_instance
  change Measure.map _ (ProbabilityTheory.cond (μ.prod (cutoffMeasure ε)) (s ×ˢ Set.univ)) = _
  rw [condition_product_on_left_event]
  have hf : Measurable (fun x : α → ℝ => fun i : {i // m i = false} => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : α)
  have hmap := Measure.map_prod_map (ProbabilityTheory.cond μ s) (cutoffMeasure ε) hf measurable_id
  change Measure.map (Prod.map (fun x : α → ℝ => fun i : {i // m i = false} => x i) id) _ = _
  rw [← hmap]
  simp only [Measure.map_id]
  rw [conditional_excluded_priority_vector_law ε hε hε1 m]
