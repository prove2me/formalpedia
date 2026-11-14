-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.exponential_interval_hazard_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:19.781913+00:00
-- url     : https://prove2.me/submissions/457b2a2c-743a-4245-9968-0c1346297e9f

import Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_tail_shift_bound
noncomputable section
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

theorem solution (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioc a (a+t)) ≤
      (1 - Real.exp (-β * t)) * (expMeasure β).real (Ioi a) ∧
    (1 - Real.exp (-β * t)) * (expMeasure β).real (Ioi a) ≤
      (β * t) * (expMeasure β).real (Ioi a) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hsub : Ioi (a+t) ⊆ Ioi a := Ioi_subset_Ioi (by linarith)
  have hd := measureReal_diff (μ := expMeasure β) hsub measurableSet_Ioi
  rw [Ioi_diff_Ioi] at hd
  have htail := exponential_tail_shift_bound β a t hβ ht
  have hlin : 1 - Real.exp (-β*t) ≤ β*t := by
    have h := Real.add_one_le_exp (-β*t)
    nlinarith
  have hmass : 0 ≤ (expMeasure β).real (Ioi a) := measureReal_nonneg
  constructor
  · rw [hd]
    nlinarith
  · exact mul_le_mul_of_nonneg_right hlin hmass
