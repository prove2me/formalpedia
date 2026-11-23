-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_eq_half_measure_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:40.988953+00:00
-- url     : https://prove2.me/submissions/00487032-23ae-49c8-bf35-2f3edb803156

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
theorem _root_.solution (n : ℕ) (z : ℝ) :
    cubeSumLawSuccDensity n z =
      (2 : ℝ≥0∞)⁻¹ * cubeSumLaw n (Set.Icc (z - 1) (z + 1)) := by
  rw [cubeSumLawSuccDensity]
  have hfun : (fun x : ℝ =>
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x)) =
      fun x : ℝ => (Set.Icc (z - 1) (z + 1)).indicator (fun _ =>
        (2 : ℝ≥0∞)⁻¹) x := by
    ext x
    have hmem : z - x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Icc (z - 1) (z + 1) := by
      constructor
      · intro h
        constructor <;> linarith [h.1, h.2]
      · intro h
        constructor <;> linarith [h.1, h.2]
    by_cases hx : x ∈ Set.Icc (z - 1) (z + 1)
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem hx]
  rw [hfun]
  rw [lintegral_indicator measurableSet_Icc]
  rw [setLIntegral_const]
end SumProduct
