-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_conj_monomial_shifted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:36:59.908699+00:00
-- url     : https://prove2.me/submissions/9e7999b6-6bf5-481c-a627-a3e73c5593db

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_conj_monomial_split
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inverseTailDifference_eq_shiftedCorrection_add_boundary
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectTailTerm_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inv_splittingY_smul_wrap_boundary

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
      infinityLeadingMonomial P r k ζ +
        (splittingY P r)⁻¹ •
          ∑ i ∈ Finset.range r.matrixRank,
            infinityShiftedCorrectionTerm P r u k i ζ := by
  rw [constantConjugatedCartwrightStegerB_conj_monomial_split]
  rw [inverseTailDifference_eq_shiftedCorrection_add_boundary]
  rw [infinityDefectTailTerm_zero]
  rw [sub_eq_add_neg]
  rw [add_assoc]
  congr 1
  exact inv_splittingY_smul_wrap_boundary P r _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
