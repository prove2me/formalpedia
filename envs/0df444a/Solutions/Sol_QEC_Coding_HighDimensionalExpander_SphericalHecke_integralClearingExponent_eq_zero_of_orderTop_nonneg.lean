-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integralClearingExponent_eq_zero_of_orderTop_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:41.712014+00:00
-- url     : https://prove2.me/submissions/84177c00-73af-4e74-b2ad-dd9b4bd751ba

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
    {k : Type u} [Field k] (f : LocalFunctionField k)
    (hf : (0 : WithTop ℤ) ≤ f.orderTop) :
    integralClearingExponent f = 0 := by
  by_cases hzero : f = 0
  · simp [hzero, integralClearingExponent]
  · have horder : (0 : ℤ) ≤ f.order := by
      have hf' := hf
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hzero] at hf'
      exact WithTop.coe_le_coe.mp hf'
    rw [integralClearingExponent, Int.toNat_eq_zero]
    exact neg_nonpos.mpr horder
end QEC.Coding.HighDimensionalExpander.SphericalHecke
