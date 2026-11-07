-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.map_smithPowerDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:47.499301+00:00
-- url     : https://prove2.me/submissions/186beb86-d4b7-4a89-a475-52091686914b

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
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (integerEmbedding k).mapMatrix
        (smithPowerDiagonal (k := k) (d := d) A) =
      (smithPowerGeneralLinearLocal (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, smithPowerDiagonal, Matrix.map_apply,
    smithPowerGeneralLinearLocal, Matrix.diagonal_apply,
    diagonalGeneralLinear_apply]
  by_cases h : i = j
  · subst j
    simp [integerEmbedding, coe_uniformizerUnit,
      HahnSeries.ofPowerSeries_X_pow]
  · simp [h]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
