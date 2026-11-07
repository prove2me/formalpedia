-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_eq_zero_of_mem_integer_and_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:51.209266+00:00
-- url     : https://prove2.me/submissions/7927b3f4-0d2f-4cf8-8047-fe169db5d0cb

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_orderTop_nonneg_of_mem_integer

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k]
    (c : Units (LocalFunctionField k))
    (hc : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k))
    (hcinv : ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k) ∈ Valued.integer (LocalFunctionField k)) :
    localUnitOrder c = 0 := by
  have hcOrder := orderTop_nonneg_of_mem_integer (c : LocalFunctionField k) hc
  have hcinvOrder := orderTop_nonneg_of_mem_integer
    (((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k)) hcinv
  rw [orderTop_coe_localUnit] at hcOrder
  rw [orderTop_coe_localUnit_inv] at hcinvOrder
  have hcInt := WithTop.coe_le_coe.mp hcOrder
  have hcinvInt := WithTop.coe_le_coe.mp hcinvOrder
  omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
