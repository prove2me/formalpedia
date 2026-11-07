-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_constantRegularMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:31.528143+00:00
-- url     : https://prove2.me/submissions/121954c4-95a5-4f6d-a2fb-290b7938d54f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (constantRegularMatrix P r a) =
      constantMultiplicationLinearMap P r a := by
  rw [constantRegularMatrix, Algebra.leftMulMatrix_apply,
    Matrix.toLin_toMatrix]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
