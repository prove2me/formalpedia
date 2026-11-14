-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.condition_finite_product_on_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:44.407192+00:00
-- url     : https://prove2.me/submissions/7e559110-d1c0-4917-b8b8-96b4966bf8a8

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem solution {α : Type} [Fintype α]
    (μ : α → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, μ i (s i) ≠ 0) :
    ProbabilityTheory.cond (Measure.pi μ) (Set.univ.pi s) =
      Measure.pi (fun i => ProbabilityTheory.cond (μ i) (s i)) := by
  classical
  haveI (i : α) : IsProbabilityMeasure (ProbabilityTheory.cond (μ i) (s i)) :=
    cond_isProbabilityMeasure_of_finite (hpos i) (measure_ne_top (μ i) (s i))
  apply Eq.symm
  apply Measure.pi_eq
  intro t ht
  rw [ProbabilityTheory.cond_apply (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    Measure.pi_pi μ, Measure.pi_pi μ]
  simp_rw [ProbabilityTheory.cond_apply (hs _)]
  rw [Finset.prod_mul_distrib]
  have hinv : (∏ i, μ i (s i))⁻¹ = ∏ i, (μ i (s i))⁻¹ := by
    apply ENNReal.prod_inv_distrib
    intro i hi j hj hij
    exact Or.inl (hpos i)
  rw [hinv]
