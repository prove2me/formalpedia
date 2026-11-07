-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueCyclicGeneratorMatrix_mul_residueConstantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:43.713225+00:00
-- url     : https://prove2.me/submissions/aa519b95-9703-4f39-88a2-b258d1124f68

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueFrobeniusMatrix_mul_residueConstantMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    residueCyclicGeneratorMatrix P r level *
        residueConstantMatrix P r level c =
      residueConstantMatrix P r level (constantFrobenius P r c) *
        residueCyclicGeneratorMatrix P r level := by
  rw [residueCyclicGeneratorMatrix, Matrix.smul_mul, Matrix.mul_smul,
    residueFrobeniusMatrix_mul_residueConstantMatrix]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
