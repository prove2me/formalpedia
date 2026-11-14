-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.proposition_2_11
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:17:54.359146+00:00
-- url     : https://prove2.me/submissions/974fe613-1b2c-445d-9fc5-83ef95f19e74

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Set ℂ) (hK : IsCompact K) (g : Ω × ℂ → ℝ≥0∞) (hg : Measurable g)
    (ζ : ℕ → Ω → ℝ≥0∞) (hζ : ∀ n, Measurable (ζ n)) :
    (∫⁻ ω, ∫⁻ z in K, g (ω,z) ∂volume ∂μ) =
      (∫⁻ z in K, ∫⁻ ω, g (ω,z) ∂μ ∂volume) ∧
    (∫⁻ ω, ∑' n, ζ n ω ∂μ) = ∑' n, ∫⁻ ω, ζ n ω ∂μ := by
  constructor
  · exact lintegral_lintegral_swap hg.aemeasurable
  · exact lintegral_tsum (fun n => (hζ n).aemeasurable)
