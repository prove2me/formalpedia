-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_toMatrix_normalBasis_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:26.734314+00:00
-- url     : https://prove2.me/submissions/92900a14-db52-42c6-a51e-b32d82867ea3

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
    LinearMap.toMatrix (frobeniusNormalBasis P .four)
        (frobeniusNormalBasis P .four)
        (constantFrobenius P .four).toLinearEquiv.toLinearMap =
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] := by
  have hrot : (finRotate 4 : Fin 4 → Fin 4) = ![1, 2, 3, 0] := by
    funext i
    fin_cases i <;> decide +kernel
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (frobeniusNormalBasis P .four).repr
    (constantFrobenius P .four (frobeniusNormalBasis P .four j)) i = _
  rw [constantFrobenius_frobeniusNormalBasis]
  rw [(frobeniusNormalBasis P .four).repr_self]
  rw [Finsupp.single_apply]
  erw [hrot]
  fin_cases i <;> fin_cases j <;> rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
