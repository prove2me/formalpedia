-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:51.912499+00:00
-- url     : https://prove2.me/submissions/459f709b-7ee3-48bc-8d54-ff2d47fe944b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass_mul_baseScalar
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BasePrime_one_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) =
      ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by
  apply Nat.mul_right_cancel (m := P.q - 1)
  · have hq := P.five_le
    omega
  · rw [natCard_constantProjectiveClass_mul_baseScalar]
    exact (geom_sum_mul_of_one_le P.one_le r.matrixRank).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
