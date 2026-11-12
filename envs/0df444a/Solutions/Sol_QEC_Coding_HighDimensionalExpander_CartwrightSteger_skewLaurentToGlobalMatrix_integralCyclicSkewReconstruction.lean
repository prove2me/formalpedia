-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_integralCyclicSkewReconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:18:59.300743+00:00
-- url     : https://prove2.me/submissions/4b5d959c-9848-44d7-abc9-9650b60c2766

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralCyclicCoordinateSkew_spec
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralCyclicCoordinate_spec
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    skewLaurentToGlobalMatrix P r
        (integralCyclicSkewReconstruction P r x hcoords) =
      ∑ p, (functionFieldCyclicBasis P r).repr x p •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
  rw [integralCyclicSkewReconstruction, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
    P r _ _ (integralCyclicCoordinateSkew_spec P r x hcoords p) p]
  rw [integralCyclicCoordinate_spec P r x hcoords p]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
