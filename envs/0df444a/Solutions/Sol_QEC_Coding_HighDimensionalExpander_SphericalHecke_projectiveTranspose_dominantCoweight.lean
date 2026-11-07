-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_dominantCoweight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:22.860508+00:00
-- url     : https://prove2.me/submissions/d6b61451-583b-4f0d-8dc7-d1e154e10dfc

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
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    projectiveTranspose (dominantCoweight k weight) =
      dominantCoweight k weight := by
  change Matrix.ProjGenLinGroup.mk
      (contragredientGeneralLinearHom
        (dominantGeneralLinear k weight)⁻¹) =
    Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k weight)
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change Matrix.transpose
    ((dominantGeneralLinear k weight :
      Matrix (Fin d) (Fin d) (LocalFunctionField k))) i j = _
  by_cases h : i = j
  · subst j
    rfl
  · simp [dominantGeneralLinear, diagonalGeneralLinear_apply, h, ne_comm]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
