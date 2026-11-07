-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinear_det_localUnitOrder_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:53.537379+00:00
-- url     : https://prove2.me/submissions/6d786ea4-414b-4ec8-b6c5-d0f6e53e46c8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_eq_zero_of_mem_integer_and_inv
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
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A)) = 0 := by
  let c := Matrix.GeneralLinearGroup.det
    (integralGeneralLinearToLocal k d A)
  have hc : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have hdet : Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A) =
      Units.map (SubringClass.subtype
        (Valued.integer (LocalFunctionField k)))
        (Matrix.GeneralLinearGroup.det A) :=
      Matrix.GeneralLinearGroup.map_det
        (SubringClass.subtype (Valued.integer (LocalFunctionField k))) A
    change ((Matrix.GeneralLinearGroup.det
      (integralGeneralLinearToLocal k d A) :
        Units (LocalFunctionField k)) : LocalFunctionField k) ∈ _
    rw [hdet]
    exact (Matrix.GeneralLinearGroup.det A).val.property
  have hcinv : ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k) ∈ Valued.integer (LocalFunctionField k) := by
    have hdetInv : c⁻¹ = Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A⁻¹) := by
      dsimp [c]
      simp
    have hmapInv : Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A⁻¹) =
      Units.map (SubringClass.subtype
        (Valued.integer (LocalFunctionField k)))
        (Matrix.GeneralLinearGroup.det A⁻¹) :=
      Matrix.GeneralLinearGroup.map_det
        (SubringClass.subtype (Valued.integer (LocalFunctionField k))) A⁻¹
    rw [hdetInv, hmapInv]
    exact (Matrix.GeneralLinearGroup.det A⁻¹).val.property
  exact localUnitOrder_eq_zero_of_mem_integer_and_inv c hc hcinv
end QEC.Coding.HighDimensionalExpander.SphericalHecke
