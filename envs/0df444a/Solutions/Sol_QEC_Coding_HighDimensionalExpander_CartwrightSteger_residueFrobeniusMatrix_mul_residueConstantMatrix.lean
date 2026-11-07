-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFrobeniusMatrix_mul_residueConstantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:41:44.639001+00:00
-- url     : https://prove2.me/submissions/032b429a-8ac3-4d52-800d-78509bf1441d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_mul_constantRegularMatrix


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    residueFrobeniusMatrix P r level * residueConstantMatrix P r level c =
      residueConstantMatrix P r level (constantFrobenius P r c) *
        residueFrobeniusMatrix P r level := by
  rw [residueFrobeniusMatrix, residueConstantMatrix,
    ← Matrix.map_mul, frobeniusGL_mul_constantRegularMatrix,
    Matrix.map_mul]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
