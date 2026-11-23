-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:29.409504+00:00
-- url     : https://prove2.me/submissions/6d773bf0-3718-4ff2-a0ac-10ff6025f3f2

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    cubeSumLawSuccDensity n 0 =
      (2 : ℝ≥0∞)⁻¹ * cubeSumLaw n (Set.Icc (-1 : ℝ) 1) := by
  rw [cubeSumLawSuccDensity]
  have hfun : (fun x : ℝ =>
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (0 - x)) =
      fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x := by
    ext x
    have hmem : 0 - x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · intro h
        constructor <;> linarith [h.1, h.2]
      · intro h
        constructor <;> linarith [h.1, h.2]
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem hx]
  rw [hfun]
  rw [lintegral_indicator measurableSet_Icc]
  rw [setLIntegral_const]
end SumProduct
