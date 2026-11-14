-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.exponential_memoryless_tail
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:42.272428+00:00
-- url     : https://prove2.me/submissions/8efdbbba-0e75-45c5-8e8f-ae36c5ea91c8

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

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

theorem solution (β d t : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioi (d+t)) =
      (expMeasure β).real (Ioi d) * (expMeasure β).real (Ioi t) := by
  rw [exponential_tail β (d+t) hβ (by linarith), exponential_tail β d hβ hd,
    exponential_tail β t hβ ht, ← Real.exp_add]
  congr 1
  ring
