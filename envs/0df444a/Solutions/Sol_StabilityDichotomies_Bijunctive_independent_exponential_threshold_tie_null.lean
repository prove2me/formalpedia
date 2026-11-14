-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.independent_exponential_threshold_tie_null
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:23.501474+00:00
-- url     : https://prove2.me/submissions/6db2830c-f954-4dd8-ab0b-8622150e3cd6

import Mathlib
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (a : Ω → ℝ) (ha : Measurable a)
    (β : ℝ) (hβ : 0 < β) :
    (expMeasure β).prod ν {z : ℝ × Ω | z.1 = a z.2} = 0 := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  haveI : NullSingletonClass (expMeasure β) := by
    unfold expMeasure gammaMeasure
    infer_instance
  have hE : MeasurableSet {z : ℝ × Ω | z.1 = a z.2} :=
    measurableSet_eq_fun measurable_fst (ha.comp measurable_snd)
  rw [Measure.prod_apply_symm hE]
  simp
