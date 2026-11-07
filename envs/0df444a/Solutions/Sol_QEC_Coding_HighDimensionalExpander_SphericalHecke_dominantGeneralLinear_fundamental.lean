-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:47.458484+00:00
-- url     : https://prove2.me/submissions/e7b7d188-3b1a-4a07-a2e0-eff0f142a9e3

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
    (k : Type u) [Field k] (d r : ℕ) :
    dominantGeneralLinear k (fundamentalDominantCoweight d r) =
      fundamentalDiagonal k d r := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [dominantGeneralLinear, fundamentalDominantCoweight,
    fundamentalDiagonal, fundamentalDiagonalUnits,
    diagonalGeneralLinear_apply]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
