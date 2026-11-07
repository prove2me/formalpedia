-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_toMatrix_normalBasis_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:25.715523+00:00
-- url     : https://prove2.me/submissions/2447b19f-607b-40bc-9509-6014ec008306

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_frobeniusNormalBasis
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    LinearMap.toMatrix (frobeniusNormalBasis P .three)
        (frobeniusNormalBasis P .three)
        (constantFrobenius P .three).toLinearEquiv.toLinearMap =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  have hrot : (finRotate 3 : Fin 3 → Fin 3) = ![1, 2, 0] := by
    funext i
    fin_cases i <;> decide +kernel
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (frobeniusNormalBasis P .three).repr
    (constantFrobenius P .three (frobeniusNormalBasis P .three j)) i = _
  rw [constantFrobenius_frobeniusNormalBasis]
  rw [(frobeniusNormalBasis P .three).repr_self]
  rw [Finsupp.single_apply]
  erw [hrot]
  fin_cases i <;> fin_cases j <;> rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
