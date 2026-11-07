-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingExponent_eq_zero_of_orderLowerBound_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:36.359403+00:00
-- url     : https://prove2.me/submissions/bd854874-aed1-49e7-9b29-8104bcb0c962

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralClearingExponent_eq_zero_of_orderTop_nonneg
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
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0 A) :
    matrixClearingExponent A = 0 := by
  classical
  have hentry : ∀ i j,
      integralClearingExponent (A i j) = 0 := by
    intro i j
    exact integralClearingExponent_eq_zero_of_orderTop_nonneg
      (A i j) (hA i j)
  simp [matrixClearingExponent, hentry]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
