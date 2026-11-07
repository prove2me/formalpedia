-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.scalarGeneralLinear_orderLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:42:36.852195+00:00
-- url     : https://prove2.me/submissions/b55dc019-3b4c-43a6-bed7-0a765a21f0a5

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
    (c : Units (LocalFunctionField k)) :
    MatrixOrderLowerBound (localUnitOrder c : WithTop ℤ)
      (Matrix.GeneralLinearGroup.scalar (Fin d) c :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [orderTop_coe_localUnit]
  · simp [hij,
      HahnSeries.orderTop_zero]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
