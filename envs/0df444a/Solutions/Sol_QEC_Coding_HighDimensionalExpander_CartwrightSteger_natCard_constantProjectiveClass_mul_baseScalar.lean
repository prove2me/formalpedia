-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass_mul_baseScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:25.434651+00:00
-- url     : https://prove2.me/submissions/8668fa57-5d91-4dec-ad9e-e5d13aaa7fa0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_baseScalarUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantExtension


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) * (P.q - 1) =
      P.q ^ r.matrixRank - 1 := by
  calc
    Nat.card (ConstantProjectiveClass P r) * (P.q - 1) =
        Nat.card (ConstantProjectiveClass P r) *
          Nat.card (baseScalarUnits P r) := by
      rw [natCard_baseScalarUnits]
    _ = Nat.card (Units (ConstantExtension P r)) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (baseScalarUnits P r)).symm
    _ = Nat.card (ConstantExtension P r) - 1 := Nat.card_units _
    _ = P.q ^ r.matrixRank - 1 := by
      rw [natCard_constantExtension]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
