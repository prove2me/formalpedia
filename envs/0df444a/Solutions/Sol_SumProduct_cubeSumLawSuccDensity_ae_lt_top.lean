-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_ae_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:51.200464+00:00
-- url     : https://prove2.me/submissions/9814674f-ff54-4d94-a27f-f8ad005afd8d

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_measurable_cubeSumLawSuccDensity
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_lintegral_ne_top

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    ∀ᵐ x : ℝ ∂volume, cubeSumLawSuccDensity n x < ∞ := by
  exact ae_lt_top (measurable_cubeSumLawSuccDensity n)
    (cubeSumLawSuccDensity_lintegral_ne_top n)
end SumProduct
