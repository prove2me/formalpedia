-- Prove2me | solution 1 for SumProduct.integrable_cubeSumLawSuccDensity_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:58.172771+00:00
-- url     : https://prove2.me/submissions/e9a4f748-7c9c-4b0f-a02d-241cd1a01541

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_integrable_cubeSumLawSuccDensity_toReal

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    Integrable (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ)) := by
  exact (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp
    (integrable_cubeSumLawSuccDensity_toReal n)
end SumProduct
