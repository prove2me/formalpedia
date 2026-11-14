-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_independent_exponential_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:47:17.380256+00:00
-- url     : https://prove2.me/submissions/dd286b4b-1db1-4a3a-bbb2-c6ea0db9b9b3

import Mathlib
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set Filter

theorem solution {α : Type} [Fintype α]
    (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ δ ∂(Measure.pi (fun _ : α => expMeasure β)), ∀ i, 0 < δ i := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hreal : (expMeasure β).real (Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq hβ 0
  have hzero : (expMeasure β) (Iic 0) = 0 := by
    have h := (ENNReal.toReal_eq_zero_iff _).mp hreal
    exact h.resolve_right (measure_ne_top _ _)
  have hone : ∀ᵐ x ∂(expMeasure β), 0 < x := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬0 < x} = Iic 0 := by ext x; simp
    rw [hset]
    exact hzero
  apply ae_all_iff.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : α => expMeasure β) (i := i)) hone
