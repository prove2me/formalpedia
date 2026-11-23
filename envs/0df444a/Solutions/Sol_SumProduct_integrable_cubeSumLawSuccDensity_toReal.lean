-- Prove2me | solution 1 for SumProduct.integrable_cubeSumLawSuccDensity_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:04:28.923481+00:00
-- url     : https://prove2.me/submissions/9dd370b8-816d-4053-a17d-9572777c31b6

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
    Integrable (fun x : ℝ => (cubeSumLawSuccDensity n x).toReal) := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_cubeSumLawSuccDensity n).aemeasurable
    (cubeSumLawSuccDensity_lintegral_ne_top n)
end SumProduct
