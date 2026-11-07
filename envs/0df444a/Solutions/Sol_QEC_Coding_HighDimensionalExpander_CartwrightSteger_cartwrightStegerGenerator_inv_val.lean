-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:04:59.241207+00:00
-- url     : https://prove2.me/submissions/36246dc4-27b4-4346-8ce2-3bdd3cddef15

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_eq_constantConjugatedB
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_inv_val

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    (((cartwrightStegerGenerator P r x)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantConjugatedBInverseExpansion P r
        (constantClassRepresentative P r x) := by
  rw [cartwrightStegerGenerator_eq_constantConjugatedB]
  exact constantConjugatedCartwrightStegerB_inv_val P r
    (constantClassRepresentative P r x)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
