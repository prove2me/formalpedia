-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:11:04.446367+00:00
-- url     : https://prove2.me/submissions/49a25423-0b47-42a8-9f2e-4de816c250a7

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_integrable_cubeSumLawSuccDensity_complex
import Theorems.Thm_SumProduct_continuousAt_cubeSumLawSuccDensity_toReal
import Theorems.Thm_SumProduct_fourier_cubeSumLawSuccDensity_eq_charFun_scaled
import Theorems.Thm_SumProduct_integrable_fourier_cubeSumLawSuccDensity
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution
    (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLawSuccDensity n 0).toReal =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
  let f : ℝ → ℂ := fun x => ((cubeSumLawSuccDensity n x).toReal : ℂ)
  have hf : Integrable f := by
    simpa [f] using integrable_cubeSumLawSuccDensity_complex n
  have hFint : Integrable (𝓕 f) := by
    simpa [f] using integrable_fourier_cubeSumLawSuccDensity n _hn
  have hv : ContinuousAt f 0 := by
    simpa [f, Function.comp_def] using
      ContinuousAt.comp
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).continuous.continuousAt)
        (continuousAt_cubeSumLawSuccDensity_toReal n _hn)
  have hinv : 𝓕⁻ (𝓕 f) 0 = f 0 := hf.fourierInv_fourier_eq hFint hv
  have hinvInt : ∫ w : ℝ, 𝓕 f w = f 0 := by
    simpa [Real.fourierInv_eq, f] using hinv
  have hinvRe : (cubeSumLawSuccDensity n 0).toReal = ∫ w : ℝ, (𝓕 f w).re := by
    have h := congrArg Complex.re hinvInt
    have h_re : ∫ w : ℝ, (𝓕 f w).re = (∫ w : ℝ, 𝓕 f w).re := by
      simpa [RCLike.re_eq_complex_re] using
        (integral_re (μ := volume) (f := fun w : ℝ => 𝓕 f w) hFint)
    rw [← h_re] at h
    simpa [f] using h.symm
  have hfour_re : (∫ w : ℝ, (𝓕 f w).re) =
      ∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re := by
    apply integral_congr_ae
    filter_upwards with w
    rw [fourier_cubeSumLawSuccDensity_eq_charFun_scaled]
  have hscale :
      (∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re) =
        (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
    have h := Measure.integral_comp_mul_left
      (fun t : ℝ => (charFun (cubeSumLaw (n + 1)) t).re) (-2 * Real.pi)
    have habs : |((-2 * Real.pi)⁻¹ : ℝ)| = (2 * Real.pi)⁻¹ := by
      rw [abs_inv]
      have hneg : (-2 * Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
      rw [abs_of_neg hneg]
      ring
    simpa [habs, smul_eq_mul, abs_of_pos Real.pi_pos, mul_comm, mul_left_comm, mul_assoc]
      using h
  calc
    (cubeSumLawSuccDensity n 0).toReal = ∫ w : ℝ, (𝓕 f w).re := hinvRe
    _ = ∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re := hfour_re
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := hscale
end SumProduct
