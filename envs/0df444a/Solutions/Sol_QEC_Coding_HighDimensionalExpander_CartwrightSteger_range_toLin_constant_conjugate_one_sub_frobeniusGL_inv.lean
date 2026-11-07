-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:27.452597+00:00
-- url     : https://prove2.me/submissions/707a6783-11e1-42de-afcf-ecd62d2da5c1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_one_sub_frobeniusGL_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_constantRegularMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (constantRegularMatrix P r (u : ConstantExtension P r) *
            (1 - ((frobeniusGL P r)⁻¹ :
              Matrix.GeneralLinearGroup
                (Fin r.matrixRank) (BaseField P))) *
            constantRegularMatrix P r
              ((u : ConstantExtension P r)⁻¹))) =
      (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r u) := by
  rw [Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
      (constantBasis P r),
    Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
      (constantBasis P r),
    toLin_constantRegularMatrix, toLin_constantRegularMatrix,
    toLin_one_sub_frobeniusGL_inv]
  let U : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := constantMultiplicationLinearMap P r u
  let B : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := frobeniusDifferenceLinearMap P r
  let V : ConstantExtension P r →ₗ[BaseField P]
      ConstantExtension P r := constantMultiplicationLinearMap P r
        ((u : ConstantExtension P r)⁻¹)
  change LinearMap.range (U.comp (B.comp V)) =
    (frobeniusDifferenceRange P r).map U
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y : ConstantExtension P r, rfl⟩
    refine ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y : ConstantExtension P r, rfl⟩, rfl⟩
    refine ⟨(u : ConstantExtension P r) * y, ?_⟩
    simp [U, B, V, LinearMap.comp_apply,
      constantMultiplicationLinearMap]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
