-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.exponential_tail_shift_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:13:28.545815+00:00
-- url     : https://prove2.me/submissions/0469db8a-3974-4dc7-a2dd-862ff2050721

import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory Set

private theorem exponential_tail_all (β a : ℝ) (hβ : 0 < β) :
    (expMeasure β).real (Ioi a) = if 0 ≤ a then Real.exp (-β * a) else 1 := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hc : (expMeasure β).real (Iic a) = if 0 ≤ a then 1 - Real.exp (-(β * a)) else 0 := by
    rw [← cdf_eq_real]
    exact cdf_expMeasure_eq hβ a
  have hh := measureReal_compl (μ := expMeasure β) (s := Iic a) measurableSet_Iic
  simp only [compl_Iic, Measure.real, measure_univ, ENNReal.toReal_one] at hh
  change (expMeasure β).real (Ioi a) = 1 - (expMeasure β).real (Iic a) at hh
  rw [hc] at hh
  split_ifs at * <;> simpa [neg_mul] using hh

theorem solution (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    Real.exp (-β * t) * (expMeasure β).real (Ioi a) ≤ (expMeasure β).real (Ioi (a+t)) := by
  rw [exponential_tail_all β a hβ, exponential_tail_all β (a+t) hβ]
  by_cases ha : 0 ≤ a
  · have hat : 0 ≤ a+t := by linarith
    simp only [ha, hat, ↓reduceIte, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases hat : 0 ≤ a+t
    · simp only [ha, hat, ↓reduceIte, mul_one]
      apply Real.exp_le_exp.mpr
      nlinarith
    · simp only [ha, hat, ↓reduceIte, mul_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith
