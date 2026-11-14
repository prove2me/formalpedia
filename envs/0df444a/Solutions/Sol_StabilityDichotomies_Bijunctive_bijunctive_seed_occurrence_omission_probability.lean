-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_seed_occurrence_omission_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:56:10.149198+00:00
-- url     : https://prove2.me/submissions/b79965ba-0508-4411-b7df-254b162af922

import Theorems.Thm_StabilityDichotomies_Bijunctive_unit_priority_omission_probability
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin I.constraints.card) :
    (bijunctiveSeedMeasure rep I ε {seed | 1 - ε / 2 < seed.1 i}).toReal = ε / 2 := by
  classical
  letI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hβ : 0 < bijunctiveRate rep ε := by
    unfold bijunctiveRate
    apply div_pos hε
    have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  letI : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := isProbabilityMeasure_expMeasure hβ
  let μP : Measure (Fin I.constraints.card → ℝ) := Measure.pi (fun _ => unitPriorityMeasure)
  let μD : Measure (Literal V → ℝ) := Measure.pi (fun _ => shiftMeasure (bijunctiveRate rep ε))
  let μC := cutoffMeasure ε
  haveI : IsProbabilityMeasure μP := by unfold μP; infer_instance
  haveI : IsProbabilityMeasure μD := by unfold μD; infer_instance
  haveI : IsProbabilityMeasure μC := by unfold μC; infer_instance
  have hfst : MeasurePreserving Prod.fst (μP.prod (μC.prod μD)) μP := measurePreserving_fst
  have hev : MeasurePreserving (fun p : Fin I.constraints.card → ℝ => p i) μP unitPriorityMeasure :=
    measurePreserving_eval (fun _ => unitPriorityMeasure) i
  have hmap := (hev.comp hfst).measure_preimage (s := Ioi (1 - ε / 2)) measurableSet_Ioi.nullMeasurableSet
  have he : (bijunctiveSeedMeasure rep I ε {seed | 1 - ε / 2 < seed.1 i}) = unitPriorityMeasure (Ioi (1 - ε / 2)) := by
    have hs : (fun x : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) => x.1 i) ⁻¹' Ioi (1 - ε / 2) = {seed | 1 - ε / 2 < seed.1 i} := by ext x; simp
    change (μP.prod (μC.prod μD)) ((fun x => x.1 i) ⁻¹' Ioi (1 - ε / 2)) = _ at hmap
    rw [hs] at hmap
    exact hmap
  rw [he,unit_priority_omission_probability ε (le_of_lt hε) hε1,ENNReal.toReal_ofReal (by linarith : 0 ≤ ε/2)]
