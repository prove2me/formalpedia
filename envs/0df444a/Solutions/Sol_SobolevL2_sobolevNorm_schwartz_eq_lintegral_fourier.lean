-- Prove2me | solution 1 for SobolevL2.sobolevNorm_schwartz_eq_lintegral_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:36:46.061814+00:00
-- url     : https://prove2.me/submissions/27419671-411b-469c-a9b8-c9c998fd2132

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

namespace Sol_SobolevL2_sobolevNorm_schwartz_eq_lintegral_fourier

variable {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If `J^s u` is represented by `f ∈ L²`, then `‖u‖_{H^s} = ‖f‖ₑ`. -/
theorem sobolevNorm_eq_of_eq [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (s : ℝ) (u : 𝓢'(E, F)) (f : Lp F 2 (volume : Measure E))
    (hf : besselPotential E F s u = f) : sobolevNorm s u = ‖f‖ₑ := by
  have hinj : ∀ g h : Lp F 2 (volume : Measure E), (g : 𝓢'(E, F)) = h → g = h := by
    intro g h hgh
    exact LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E)) (p := 2)) hgh
  unfold sobolevNorm
  apply le_antisymm
  · exact iInf₂_le (α := ℝ≥0∞) f hf
  · refine le_iInf₂ fun g hg => ?_
    rw [hinj g f (hg.symm.trans hf)]

/-- The Bessel potential of a Schwartz function is the Schwartz function
`𝓕⁻ ((1 + ‖ξ‖²)^{s/2} • 𝓕 φ)`. -/
theorem besselPotential_schwartz [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (s : ℝ) (φ : 𝓢(E, F)) :
    besselPotential E F s (φ : 𝓢'(E, F)) =
      (((SchwartzMap.fourierMultiplierCLM F (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) φ).toLp 2 :
        Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  exact SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)) φ

/-- Plancherel for Schwartz functions, in `ℝ≥0∞`. -/
theorem enorm_toLp_fourier [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (g : 𝓢(E, F)) :
    ‖(𝓕 g).toLp 2 (volume : Measure E)‖ₑ = ‖g.toLp 2 (volume : Measure E)‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  ext
  exact SchwartzMap.norm_fourier_toL2_eq g

/-- The `L²` norm of a Schwartz function as a lower Lebesgue integral. -/
theorem enorm_toLp_two [NormedAddCommGroup F] [NormedSpace ℝ F] (g : 𝓢(E, F)) :
    ‖g.toLp 2 (volume : Measure E)‖ₑ = (∫⁻ x : E, ‖g x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp g 2 volume),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

end Sol_SobolevL2_sobolevNorm_schwartz_eq_lintegral_fourier

open Sol_SobolevL2_sobolevNorm_schwartz_eq_lintegral_fourier in
theorem solution {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (φ : 𝓢(E, F)) :
    sobolevNorm s (φ : 𝓢'(E, F)) =
      (∫⁻ ξ : E, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) * ‖𝓕 (φ : E → F) ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have hm : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)
  rw [sobolevNorm_eq_of_eq s _ _ (besselPotential_schwartz s φ), ← enorm_toLp_fourier,
    SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    enorm_toLp_two]
  congr 1
  refine lintegral_congr fun ξ => ?_
  have h0 : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, enorm_smul, mul_pow,
    Real.enorm_eq_ofReal (Real.rpow_nonneg h0 _), ← ENNReal.ofReal_pow (Real.rpow_nonneg h0 _),
    ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 3
  · push_cast; ring
