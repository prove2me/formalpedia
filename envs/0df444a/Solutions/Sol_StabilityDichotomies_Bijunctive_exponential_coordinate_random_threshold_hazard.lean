-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.exponential_coordinate_random_threshold_hazard
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:22.219227+00:00
-- url     : https://prove2.me/submissions/0322d155-2659-4811-bc9a-0ba3f91bd6d0

import Theorems.Thm_StabilityDichotomies_Bijunctive_independent_random_threshold_hazard
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

theorem solution (n : ℕ) (i : Fin (n+1))
    (a : (Fin n → ℝ) → ℝ) (ha : Measurable a) (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin (n+1) => expMeasure β)
      {δ | a (i.removeNth δ) < δ i ∧ δ i ≤ a (i.removeNth δ) + t}) ≤
      ENNReal.ofReal (1 - Real.exp (-β*t)) *
        (Measure.pi (fun _ : Fin (n+1) => expMeasure β)
          {δ | a (i.removeNth δ) < δ i}) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  have hE : MeasurableSet {z : ℝ × (Fin n → ℝ) | a z.2 < z.1 ∧ z.1 ≤ a z.2+t} :=
    (measurableSet_lt (ha.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((ha.comp measurable_snd).add_const t))
  have hW : MeasurableSet {z : ℝ × (Fin n → ℝ) | a z.2 < z.1} :=
    measurableSet_lt (ha.comp measurable_snd) measurable_fst
  have hMP := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => expMeasure β) i
  have hEeq := hMP.measure_preimage hE.nullMeasurableSet
  have hWeq := hMP.measure_preimage hW.nullMeasurableSet
  have h := independent_random_threshold_hazard ν a ha β t hβ ht
  rw [← hWeq] at h
  have hh := hEeq.le.trans h
  simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] using hh
