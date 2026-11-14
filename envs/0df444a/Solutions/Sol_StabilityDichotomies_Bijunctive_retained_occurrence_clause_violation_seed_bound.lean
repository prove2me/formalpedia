-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.retained_occurrence_clause_violation_seed_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:55:34.390002+00:00
-- url     : https://prove2.me/submissions/f3835a64-c506-4bcf-b28e-d2062c306d64

import Theorems.Thm_StabilityDichotomies_Bijunctive_retained_clause_violation_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_product_probability_le_ae_fiber_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_nested_bijunctive_subinstances
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_predicate_event_measurable
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (i : Fin I.constraints.card)
    (q : Clause (Fin (occurrenceAt I i).rel.val.arity)) (hq : q ∈ rep.clauses (occurrenceAt I i).rel)
    (ht : (substituteClause (occurrenceAt I i) q).1 ≠ literalNeg (substituteClause (occurrenceAt I i) q).2) :
    (bijunctiveSeedMeasure rep I ε
      {seed | seed.1 i ≤ 1 - ε / 2 ∧
        ¬ clauseSatisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)
          (substituteClause (occurrenceAt I i) q)}).toReal ≤
      1 - Real.exp (-bijunctiveRate rep ε) := by
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
  letI : IsProbabilityMeasure (expMeasure (bijunctiveRate rep ε)) := isProbabilityMeasure_expMeasure hβ
  letI : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := isProbabilityMeasure_expMeasure hβ
  let μP : Measure (Fin I.constraints.card → ℝ) := Measure.pi (fun _ => unitPriorityMeasure)
  let μD : Measure (Literal V → ℝ) := Measure.pi (fun _ => shiftMeasure (bijunctiveRate rep ε))
  let μC := cutoffMeasure ε
  let E : Set ((Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) :=
    {seed | seed.1 i ≤ 1 - ε / 2 ∧ ¬ clauseSatisfied
      (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2) (substituteClause (occurrenceAt I i) q)}
  let z : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-bijunctiveRate rep ε))
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact measurableSet_le ((measurable_pi_apply i).comp measurable_fst) measurable_const
    · exact bijunctive_output_predicate_event_measurable rep I ε
        (fun x => ¬ clauseSatisfied x (substituteClause (occurrenceAt I i) q))
  haveI : IsProbabilityMeasure μP := by unfold μP; infer_instance
  haveI : IsProbabilityMeasure μD := by unfold μD; infer_instance
  haveI : IsProbabilityMeasure μC := by unfold μC; infer_instance
  have hbound : (μP.prod (μC.prod μD)) E ≤ z := by
    apply product_probability_le_ae_fiber_bound μP (μC.prod μD) E hE z
    apply Filter.Eventually.of_forall
    intro p
    let E' : Set (ℝ × (Literal V → ℝ)) := Prod.mk p ⁻¹' E
    have hE' : MeasurableSet E' := hE.preimage (measurable_const.prodMk measurable_id)
    apply product_probability_le_ae_fiber_bound μC μD E' hE' z
    have hcut : ∀ᵐ t ∂μC, 1 - ε / 2 ≤ t := by
      have h := ProbabilityTheory.ae_cond_mem (μ := volume) (s := Icc (1 - ε / 2) 1) measurableSet_Icc
      filter_upwards [h] with t ht'
      exact ht'.1
    filter_upwards [hcut] with t ht'
    by_cases hi : p i ≤ 1 - ε / 2
    · have hn := nested_bijunctive_subinstances I hI ε t p ht'
      let G := thinnedInstance I (fun i => decide (p i ≤ 1 - ε / 2))
      let F := thinnedInstance I (fun i => decide (p i ≤ t))
      have hreal := retained_clause_violation_bound rep G F hn.1 hn.2.1
        (occurrenceAt I i) (hn.2.2 i hi) q hq ht (bijunctiveRate rep ε) hβ
      have hle := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_toReal (measure_ne_top (Measure.pi (fun _ : Literal V => expMeasure (bijunctiveRate rep ε))) _)] at hle
      simpa [E',E,G,F,bijunctiveOutput,μD,shiftMeasure,z,hi] using hle
    · have hzero : {x : Literal V → ℝ | (t,x) ∈ E'} = ∅ := by
        ext x
        simp [E',E,hi]
      rw [hzero,measure_empty]
      exact bot_le
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hz : 0 ≤ 1 - Real.exp (-bijunctiveRate rep ε) := by
    have h := Real.exp_le_one_iff.mpr (show -bijunctiveRate rep ε ≤ 0 by linarith)
    linarith
  simpa [bijunctiveSeedMeasure, μP, μC, μD, E, z, ENNReal.toReal_ofReal hz] using hreal
