-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.inverseTailDifference_eq_shiftedCorrection_add_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:32:39.202476+00:00
-- url     : https://prove2.me/submissions/0dd83172-e1a0-4ee9-bcd0-ca06b71b872b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLeadingMonomial_mul_inverseTail
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectMonomial_mul_inverseTail
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLeadingTailTerm_sub_defectTailTerm_succ
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectTailTerm_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sum_sub_sum_eq_sum_sub_succ_add_boundary

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingMonomial P r k ζ *
          constantConjugatedBInverseTail P r u -
        infinityDefectMonomial P r u k ζ *
          constantConjugatedBInverseTail P r u =
      (∑ i ∈ Finset.range r.matrixRank,
          infinityShiftedCorrectionTerm P r u k i ζ) +
        (onePlusY P r) • infinityDefectTailTerm P r u k 0 ζ -
          infinityDefectTailTerm P r u k 0 ζ := by
  rw [infinityLeadingMonomial_mul_inverseTail,
    infinityDefectMonomial_mul_inverseTail]
  change
    (∑ i ∈ Finset.range r.matrixRank,
        infinityLeadingTailTerm P r u k i ζ) -
      (∑ i ∈ Finset.range r.matrixRank,
        infinityDefectTailTerm P r u k i ζ) = _
  rw [sum_sub_sum_eq_sum_sub_succ_add_boundary]
  rw [infinityDefectTailTerm_rank]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact infinityLeadingTailTerm_sub_defectTailTerm_succ P r u k i ζ
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
