-- Prove2me | solution 1 for OnlineNRM.TSFixed.meanDemand_coordinate_bounds_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T15:00:58.776195+00:00
-- url     : https://prove2.me/submissions/ed192d72-682e-4f4d-9581-cc11f3ef2461

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (dbar : Fin N → ℝ)
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    (i : Fin N) (k : Fin K) :
    Measurable (fun ρ => meanDemand F ρ i k) ∧
      ∀ ρ, meanDemand F ρ i k ∈ Set.Icc 0 (dbar i) := by
  constructor
  · change Measurable (fun ρ => ∫ x, x i ∂F (ρ, k))
    have hsm : StronglyMeasurable (fun x : Fin N → ℝ => x i) :=
      (continuous_apply i).stronglyMeasurable
    have hkernel : StronglyMeasurable
        (fun z : Θ × Fin K => ∫ x, x i ∂F z) :=
      hsm.integral_kernel
    exact hkernel.measurable.comp (measurable_id.prodMk measurable_const)
  · intro ρ
    let μ := F (ρ, k)
    have hprob : IsProbabilityMeasure μ := inferInstance
    have hbound := hF ρ k
    have hmeas : AEStronglyMeasurable (fun x : Fin N → ℝ => x i) μ :=
      (continuous_apply i).measurable.aestronglyMeasurable
    have hnorm : ∀ᵐ x ∂μ, ‖x i‖ ≤ max 0 (dbar i) := by
      filter_upwards [hbound] with x hx
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [hx i |>.1, le_max_left 0 (dbar i)]
      · exact le_trans (hx i).2 (le_max_right 0 (dbar i))
    have hint : Integrable (fun x : Fin N → ℝ => x i) μ := by
      apply (integrable_const (max 0 (dbar i))).mono' hmeas
      filter_upwards [hnorm] with x hx
      simpa only [Real.norm_eq_abs] using hx
    have hlo : 0 ≤ ∫ x, x i ∂μ := by
      have h := integral_mono_ae (integrable_const (0 : ℝ)) hint
        (hbound.mono fun x hx => (hx i).1)
      simpa using h
    have hhi : (∫ x, x i ∂μ) ≤ dbar i := by
      have h := integral_mono_ae hint (integrable_const (dbar i))
        (hbound.mono fun x hx => (hx i).2)
      simpa [μ] using h
    change (∫ x, x i ∂μ) ∈ Set.Icc 0 (dbar i)
    exact ⟨hlo, hhi⟩