-- Prove2me | solution 1 for RiskControl.Optimal.expSize_le_of_setdiff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:52:48.6151+00:00
-- url     : https://prove2.me/submissions/2c6e56ef-59b7-4be1-b20e-c8ea5c411acb

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RiskControl.Optimal

theorem solution {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (A B : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1})
    (hB : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ B q.1})
    (h : ∫⁻ x, μ (A x \ B x) ∂P.fst ≤ ∫⁻ x, μ (B x \ A x) ∂P.fst) :
    expSize P μ A ≤ expSize P μ B := by
  unfold expSize
  have hAx : ∀ x, MeasurableSet (A x) := fun x => measurable_prodMk_left hA
  have hBx : ∀ x, MeasurableSet (B x) := fun x => measurable_prodMk_left hB
  have hmeas : ∀ (C D : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ C q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ D q.1} → Measurable (fun x => μ (C x ∩ D x)) := by
    intro C D hC hD
    have := hC.inter hD
    exact measurable_measure_prodMk_left (ν := μ) this
  have hdiff : ∀ (C D : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ C q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ D q.1} → Measurable (fun x => μ (C x \ D x)) := by
    intro C D hC hD
    have := hC.inter hD.compl
    exact measurable_measure_prodMk_left (ν := μ) this
  have e1 : ∀ x, μ (A x) = μ (A x \ B x) + μ (A x ∩ B x) := fun x =>
    (measure_diff_add_inter (A x) (hBx x)).symm
  have e2 : ∀ x, μ (B x) = μ (B x \ A x) + μ (A x ∩ B x) := fun x => by
    rw [Set.inter_comm]; exact (measure_diff_add_inter (B x) (hAx x)).symm
  simp_rw [e1, e2]
  rw [lintegral_add_left (hdiff A B hA hB), lintegral_add_left (hdiff B A hB hA)]
  exact add_le_add h le_rfl
