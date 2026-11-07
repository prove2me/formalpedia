-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLeadingTailTerm_sub_defectTailTerm_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:29:18.141842+00:00
-- url     : https://prove2.me/submissions/b4ffc55c-8b31-42a8-9136-9f527622ff78

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mul_pow_succ
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityTailCoefficient_sub_succ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingTailTerm P r u k i ζ -
        infinityDefectTailTerm P r u k (i + 1) ζ =
      infinityShiftedCorrectionTerm P r u k i ζ := by
  rw [infinityLeadingTailTerm, infinityDefectTailTerm,
    infinityShiftedCorrectionTerm]
  have hexponent : k + (i + 1) = (k + i) + 1 := by omega
  rw [hexponent]
  rw [mul_assoc
    (constantMatrix P r
      ((infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
        (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k)
            (infinityCyclicCoefficient P r u (i + 1) :
              ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ (k + i + 1))]
  rw [cyclicGeneratorInverseMatrix_mul_pow_succ]
  rw [← sub_mul]
  change
    (constantMatrixEmbedding P r
          (ζ * (constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)) -
      constantMatrixEmbedding P r
          ((infinityCyclicInverseCoefficient P r u *
              (constantFrobenius P r).symm ζ) *
            (constantFrobenius P r).symm
              ((constantFrobenius P r ^ k)
                (infinityCyclicCoefficient P r u (i + 1) :
                  ConstantExtension P r)))) *
        cyclicGeneratorMatrix P r ^ (k + i) = _
  rw [← map_sub, infinityTailCoefficient_sub_succ]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
