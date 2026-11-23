-- Prove2me | solution 1 for SumProduct.integrable_fourier_cubeSumLawSuccDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:07:31.738246+00:00
-- url     : https://prove2.me/submissions/f5248cae-d288-4b5e-8ba9-89fd6e7752cf

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_charFun_cubeSumLaw_eq_sinc_pow
import Theorems.Thm_SumProduct_fourier_cubeSumLawSuccDensity_eq_charFun_scaled
import Theorems.Thm_SumProduct_integrable_sinc_pow
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
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Integrable (𝓕 (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ))) := by
  have hsinc : Integrable (fun t : ℝ => (Real.sinc t) ^ (n + 1)) := by
    exact integrable_sinc_pow (Nat.succ_le_succ hn)
  have hscale_ne : (-2 * Real.pi) ≠ (0 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hsinc_scaled :
      Integrable (fun w : ℝ => (Real.sinc ((-2 * Real.pi) * w)) ^ (n + 1)) :=
    hsinc.comp_mul_left' hscale_ne
  have hcomplex_scaled : Integrable
      (fun w : ℝ => ((Real.sinc ((-2 * Real.pi) * w) : ℂ) ^ (n + 1))) := by
    simpa using (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp hsinc_scaled
  have hchar_scaled : Integrable
      (fun w : ℝ => charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)) := by
    refine hcomplex_scaled.congr ?_
    filter_upwards with w
    rw [charFun_cubeSumLaw_eq_sinc_pow]
  refine hchar_scaled.congr ?_
  filter_upwards with w
  exact (fourier_cubeSumLawSuccDensity_eq_charFun_scaled n w).symm
end SumProduct
