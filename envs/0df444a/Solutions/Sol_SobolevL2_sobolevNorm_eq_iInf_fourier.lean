-- Prove2me | solution 1 for SobolevL2.sobolevNorm_eq_iInf_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:24:15.800172+00:00
-- url     : https://prove2.me/submissions/82b46fa8-c768-4e8c-b812-9517548ce756

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢'(E, F)) :
    sobolevNorm s u =
      ⨅ (g : Lp F 2 (volume : Measure E))
        (_ : smulLeftCLM F (fun ξ : E ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 u) = g), ‖g‖ₑ := by
  -- Plancherel in `ℝ≥0∞`
  have henorm : ∀ f : Lp F 2 (volume : Measure E), ‖𝓕 f‖ₑ = ‖f‖ₑ := by
    intro f
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    ext
    exact Lp.norm_fourier_eq f
  unfold sobolevNorm
  apply le_antisymm
  · refine le_iInf₂ fun g hg => ?_
    refine (iInf₂_le (𝓕⁻ g) ?_).trans_eq ?_
    · rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply, hg,
        Lp.fourierInv_toTemperedDistribution_eq g]
    · rw [← henorm (𝓕⁻ g), FourierTransform.fourier_fourierInv_eq]
  · refine le_iInf₂ fun f hf => ?_
    refine (iInf₂_le (𝓕 f) ?_).trans_eq (henorm f)
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply, hf,
      Lp.fourier_toTemperedDistribution_eq f]
