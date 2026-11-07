-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.orderTop_nonneg_of_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:46:12.821977+00:00
-- url     : https://prove2.me/submissions/5653a302-635f-433b-84c7-70ceaa3d2ef8

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
    {k : Type u} [Field k] (x : LocalFunctionField k)
    (hx : x ∈ Valued.integer (LocalFunctionField k)) :
    (0 : WithTop ℤ) ≤ x.orderTop := by
  rw [Valuation.mem_integer_iff] at hx
  obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe k x).1 hx
  rw [← hF, HahnSeries.zero_le_orderTop_iff]
  by_contra hnonneg
  have hneg : (F : LocalFunctionField k).order < 0 := lt_of_not_ge hnonneg
  have hcoeff :
      (F : LocalFunctionField k).coeff (F : LocalFunctionField k).order = 0 := by
    rw [PowerSeries.coeff_coe]
    simp [hneg]
  have hzero : (F : LocalFunctionField k) = 0 :=
    HahnSeries.coeff_order_eq_zero.mp hcoeff
  rw [hzero, HahnSeries.order_zero] at hneg
  exact (lt_irrefl 0 hneg)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
