-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToLocal_permutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:55.385765+00:00
-- url     : https://prove2.me/submissions/9348d209-9f1e-494e-b4c5-a98d5f286f3b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
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
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    powerSeriesGeneralLinearToLocal k d
        (permutationGeneralLinear (IntegerRing k) σ) =
      permutationGeneralLinear (LocalFunctionField k) σ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [powerSeriesGeneralLinearToLocal, permutationGeneralLinear,
    Matrix.GeneralLinearGroup.map_apply, integerEmbedding,
    Equiv.Perm.permMatrix, PEquiv.toMatrix]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
