-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_det_localUnitOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:47:37.487831+00:00
-- url     : https://prove2.me/submissions/2d577ad7-bac5-4e2d-b2a4-278f6ad223aa

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_prod
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ}
    (weight : DominantCoweight d) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (dominantGeneralLinear k weight)) =
      ∑ i, (weight.exponent i : ℤ) := by
  have hdet : Matrix.GeneralLinearGroup.det
      (dominantGeneralLinear k weight) =
      ∏ i, uniformizerUnit k ^ weight.exponent i := by
    apply Units.ext
    simp [dominantGeneralLinear, diagonalGeneralLinear,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdet, localUnitOrder_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact localUnitOrder_uniformizerUnit_pow _
end QEC.Coding.HighDimensionalExpander.SphericalHecke
