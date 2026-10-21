-- Prove2me | solution 1 for RiskControl.Optimal.lintegral_condLoss
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:57:10.227983+00:00
-- url     : https://prove2.me/submissions/4db426ac-db23-4ca1-91a3-d2fd3cb39827

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RiskControl.Optimal

theorem solution {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (A : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1}) :
    ∫⁻ p, ∫⁻ z in A p.1, (ℓ p.2 z : ℝ≥0∞) ∂μ ∂P
      = ∫⁻ x, ∫⁻ z in A x, condLoss κ ℓ x z ∂μ ∂P.fst := by
  classical
  have hAx : ∀ x, MeasurableSet (A x) := fun x => measurable_prodMk_left hA
  -- the jointly measurable integrand
  let H : (𝒳 × 𝒴) × 𝒵 → ℝ≥0∞ := fun q => if q.2 ∈ A q.1.1 then (ℓ q.1.2 q.2 : ℝ≥0∞) else 0
  have hHmeas : Measurable H := by
    have hset : MeasurableSet {q : (𝒳 × 𝒴) × 𝒵 | q.2 ∈ A q.1.1} :=
      hA.preimage (f := fun q : (𝒳 × 𝒴) × 𝒵 => (q.1.1, q.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hl : Measurable (fun q : (𝒳 × 𝒴) × 𝒵 => (ℓ q.1.2 q.2 : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp (hℓ.comp (f := fun q : (𝒳 × 𝒴) × 𝒵 => (q.1.2, q.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact Measurable.ite hset hl measurable_const
  have hlhs : ∀ p : 𝒳 × 𝒴, ∫⁻ z in A p.1, (ℓ p.2 z : ℝ≥0∞) ∂μ = ∫⁻ z, H (p, z) ∂μ := by
    intro p
    rw [← lintegral_indicator (hAx p.1)]
    apply lintegral_congr
    intro z
    simp [H, Set.indicator]
  simp_rw [hlhs]
  have hfm : Measurable (fun p : 𝒳 × 𝒴 => ∫⁻ z, H (p, z) ∂μ) :=
    hHmeas.lintegral_prod_right'
  have e1 : ∫⁻ p, ∫⁻ z, H (p, z) ∂μ ∂P = ∫⁻ p, ∫⁻ z, H (p, z) ∂μ ∂(P.fst ⊗ₘ κ) := by rw [hκ]
  rw [e1, Measure.lintegral_compProd hfm]
  apply lintegral_congr
  intro x
  have hm2 : Measurable (fun q : 𝒴 × 𝒵 => H ((x, q.1), q.2)) :=
    hHmeas.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable, ← lintegral_indicator (hAx x)]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A x
  · simp [H, hz, Set.indicator, condLoss]
  · simp [H, hz, Set.indicator]
