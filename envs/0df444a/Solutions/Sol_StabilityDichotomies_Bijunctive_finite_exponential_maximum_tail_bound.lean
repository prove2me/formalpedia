-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_exponential_maximum_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:09:11.725189+00:00
-- url     : https://prove2.me/submissions/37156b1f-9dd5-4006-9bc3-9f7468c43236

import Mathlib
noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

private theorem exponential_tail (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioi t) = Real.exp (-β * t) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hc : (expMeasure β).real (Iic t) = 1 - Real.exp (-(β * t)) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq hβ t]
    simp [ht]
  have hh := measureReal_compl (μ := expMeasure β) (s := Iic t) measurableSet_Iic
  simp only [compl_Iic, Measure.real, measure_univ, ENNReal.toReal_one] at hh
  change (expMeasure β).real (Ioi t) = 1 - (expMeasure β).real (Iic t) at hh
  rw [hc] at hh
  simpa [neg_mul] using hh

theorem solution {α : Type} [Fintype α]
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    ((Measure.pi (fun _ : α => expMeasure β)) {δ : α → ℝ | ∃ i, t < δ i}).toReal ≤
      (Fintype.card α : ℝ) * Real.exp (-β*t) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have heq : {δ : α → ℝ | ∃ i, t < δ i} = ⋃ i : α, {δ | t < δ i} := by ext δ; simp
  have hcoord (i : α) : μ.real {δ | t < δ i} = Real.exp (-β*t) := by
    have hmp := measurePreserving_eval (fun _ : α => expMeasure β) i
    have hh := hmp.measure_preimage (s := Ioi t) measurableSet_Ioi.nullMeasurableSet
    have hs : (fun δ : α → ℝ => δ i) ⁻¹' Ioi t = {δ | t < δ i} := by ext δ; simp
    rw [hs] at hh
    change μ {δ | t < δ i} = _ at hh
    rw [Measure.real,hh]
    exact exponential_tail β t hβ ht
  rw [heq]
  calc
    μ.real (⋃ i : α, {δ | t < δ i}) ≤ ∑ i : α, μ.real {δ | t < δ i} := measureReal_iUnion_fintype_le _
    _ = (Fintype.card α : ℝ) * Real.exp (-β*t) := by simp [hcoord]
