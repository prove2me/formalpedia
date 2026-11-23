-- Prove2me | solution 1 for SumProduct.continuousAt_cubeSumLawSuccDensity_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:09:34.310498+00:00
-- url     : https://prove2.me/submissions/46012398-4d47-4c9b-944f-62b7a1595099

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_integrable_cubeSumLawSuccDensity_toReal
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
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
    (n : ℕ) (hn : 1 ≤ n) :
    ContinuousAt (fun z : ℝ => (cubeSumLawSuccDensity n z).toReal) 0 := by
  let g : ℝ → ℝ := fun x => (cubeSumLawSuccDensity (n - 1) x).toReal
  have hg : Integrable g := by
    simpa [g] using integrable_cubeSumLawSuccDensity_toReal (n - 1)
  have hprim : Continuous (fun b : ℝ => ∫ x in (-1 : ℝ)..b, g x) :=
    hg.continuous_primitive (-1)
  have hcont : Continuous (fun z : ℝ =>
      (1 / 2 : ℝ) *
        ((∫ x in (-1 : ℝ)..(z + 1), g x) - ∫ x in (-1 : ℝ)..(z - 1), g x)) := by
    exact continuous_const.mul
      ((hprim.comp (continuous_id.add continuous_const)).sub
        (hprim.comp (continuous_id.sub continuous_const)))
  have heq : (fun z : ℝ => (cubeSumLawSuccDensity n z).toReal) =
      fun z : ℝ => (1 / 2 : ℝ) *
        ((∫ x in (-1 : ℝ)..(z + 1), g x) - ∫ x in (-1 : ℝ)..(z - 1), g x) := by
    ext z
    rw [cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral n hn z]
    have h1 : IntervalIntegrable g volume (-1 : ℝ) (z + 1) := hg.intervalIntegrable
    have h2 : IntervalIntegrable g volume (-1 : ℝ) (z - 1) := hg.intervalIntegrable
    rw [← intervalIntegral.integral_interval_sub_left h1 h2]
  rw [heq]
  exact hcont.continuousAt
end SumProduct
