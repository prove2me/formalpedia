-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.independent_random_threshold_hazard
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:20.811525+00:00
-- url     : https://prove2.me/submissions/574e551e-1222-4899-9859-0272a4b0b56b

import Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_interval_hazard_bound
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (a : Ω → ℝ) (ha : Measurable a)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    ((expMeasure β).prod ν {z : ℝ × Ω | a z.2 < z.1 ∧ z.1 ≤ a z.2 + t}) ≤
      ENNReal.ofReal (1 - Real.exp (-β*t)) *
        ((expMeasure β).prod ν {z : ℝ × Ω | a z.2 < z.1}) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hE : MeasurableSet {z : ℝ × Ω | a z.2 < z.1 ∧ z.1 ≤ a z.2+t} := by
    exact (measurableSet_lt (ha.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((ha.comp measurable_snd).add_const t))
  have hW : MeasurableSet {z : ℝ × Ω | a z.2 < z.1} :=
    measurableSet_lt (ha.comp measurable_snd) measurable_fst
  rw [Measure.prod_apply_symm hE, Measure.prod_apply_symm hW]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-β*t)) *
      (expMeasure β) (Ioi (a y)) ∂ν := by
      apply lintegral_mono
      intro y
      change (expMeasure β) (Ioc (a y) (a y+t)) ≤ _
      have hh := (exponential_interval_hazard_bound β (a y) t hβ ht).1
      have hcoef : 0 ≤ 1 - Real.exp (-β*t) := by
        have he : Real.exp (-β*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      have hm := ENNReal.ofReal_le_ofReal hh
      rw [ENNReal.ofReal_mul hcoef] at hm
      unfold Measure.real at hm
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)] at hm
      exact hm
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
