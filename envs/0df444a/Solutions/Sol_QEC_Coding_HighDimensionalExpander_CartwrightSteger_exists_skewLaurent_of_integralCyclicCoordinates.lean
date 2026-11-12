-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralCyclicCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:22:39.394295+00:00
-- url     : https://prove2.me/submissions/9971aa91-a6a0-4a2c-8146-3de8b2e83736

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_sum_repr_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f = x.1 := by
  refine ⟨integralCyclicSkewReconstruction P r x hcoords, ?_⟩
  rw [skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction,
    functionFieldCyclicBasis_sum_repr_coe]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
