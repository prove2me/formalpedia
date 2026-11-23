-- Prove2me | solution 1 for SumProduct.measurable_cubeSumLawSuccDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:57:48.436314+00:00
-- url     : https://prove2.me/submissions/0201ce4c-9232-4a65-97ee-9996b2bd700c

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
    Measurable (cubeSumLawSuccDensity n) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun z x =>
    (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x)
  have hF : Measurable (Function.uncurry F) :=
    (measurable_const.indicator measurableSet_Icc).comp
      (measurable_fst.sub measurable_snd)
  exact hF.lintegral_prod_right
end SumProduct
