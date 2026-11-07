-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:32:34.071822+00:00
-- url     : https://prove2.me/submissions/07bfde89-a417-44eb-9bdb-fc73f047905d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_val

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    (constantConjugatedCartwrightStegerB P r u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k) =
      constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        constantMatrix P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ k := by
  rw [constantConjugatedCartwrightStegerB_val, sub_mul, one_mul]
  rw [mul_assoc]
  rw [← mul_assoc (cyclicGeneratorInverseMatrix P r)
    (constantMatrix P r ζ) (cyclicGeneratorMatrix P r ^ k)]
  rw [cyclicGeneratorInverseMatrix_mul_constantMatrix]
  rw [← mul_assoc
    (constantMatrix P r (infinityCyclicInverseCoefficient P r u))
    (constantMatrix P r ((constantFrobenius P r).symm ζ) *
      cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ k)]
  rw [← mul_assoc
    (constantMatrix P r (infinityCyclicInverseCoefficient P r u))
    (constantMatrix P r ((constantFrobenius P r).symm ζ))
    (cyclicGeneratorInverseMatrix P r)]
  change
    constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        (constantMatrixEmbedding P r (infinityCyclicInverseCoefficient P r u) *
          constantMatrixEmbedding P r ((constantFrobenius P r).symm ζ)) *
          cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r ^ k = _
  rw [← map_mul]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
