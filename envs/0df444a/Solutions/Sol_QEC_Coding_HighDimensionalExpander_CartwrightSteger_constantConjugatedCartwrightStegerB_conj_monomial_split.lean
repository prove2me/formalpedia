-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:35:37.562762+00:00
-- url     : https://prove2.me/submissions/790f8871-fd17-4926-88d3-6112cdf276d7

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedBInverseExpansion_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_matrix_sub_mul_one_add_smul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_preExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityLeadingMonomial P r k ζ -
          infinityDefectMonomial P r u k ζ +
        (splittingY P r)⁻¹ •
          (infinityLeadingMonomial P r k ζ *
              constantConjugatedBInverseTail P r u -
            infinityDefectMonomial P r u k ζ *
              constantConjugatedBInverseTail P r u) := by
  rw [infinityLeadingMonomial, infinityDefectMonomial]
  rw [constantConjugatedCartwrightStegerB_conj_monomial_preExpansion]
  rw [constantConjugatedBInverseExpansion_eq]
  exact matrix_sub_mul_one_add_smul _ _ _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
