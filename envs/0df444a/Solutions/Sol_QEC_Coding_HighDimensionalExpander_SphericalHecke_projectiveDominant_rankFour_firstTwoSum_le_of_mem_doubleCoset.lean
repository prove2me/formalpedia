-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:11:39.040477+00:00
-- url     : https://prove2.me/submissions/1fc4b5a3-6ce0-4219-b063-993a924ade01

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalarGeneralLinear_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompound_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_secondCompound_inv_first_entry_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) ≤
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  let leftLocal := integralGeneralLinearToLocal k 4 left
  let rightLocal := integralGeneralLinearToLocal k 4 right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin 4) c
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hscalarInv : MatrixOrderLowerBound 0
      ((scalar⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) := by
    rw [show scalar⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 4) c⁻¹ by
      exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv, hc] using
      (scalarGeneralLinear_orderLowerBound (d := 4) c⁻¹)
  have hrightCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hrightInv
  have hleftCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hleftInv
  have hscalarCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear scalar)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hscalarInv
  have hdiagonalBCompoundInv :=
    projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
      (k := k) b
  have hinverse :
      diagonalA⁻¹ =
        rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hcompoundInverse :
      (rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ =
        (rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalar)⁻¹ := by
    have h := congrArg rankFourSecondCompoundGeneralLinear hinverse
    rw [rankFourSecondCompoundGeneralLinear_inv] at h
    rw [rankFourSecondCompoundGeneralLinear_mul,
      rankFourSecondCompoundGeneralLinear_mul,
      rankFourSecondCompoundGeneralLinear_mul] at h
    rw [rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv,
      rankFourSecondCompoundGeneralLinear_inv] at h
    exact h
  have hproduct : MatrixOrderLowerBound
      ((-((b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalar)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    simpa only [zero_add, add_zero, Units.val_mul, diagonalB] using
      (((hrightCompoundInv.mul hdiagonalBCompoundInv).mul
        hleftCompoundInv).mul hscalarCompoundInv)
  have hboundA : MatrixOrderLowerBound
      ((-((b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [hcompoundInverse]
    exact hproduct
  have hentry := hboundA (0 : Fin 6) 0
  dsimp [diagonalA] at hentry
  rw [projectiveDominant_rankFour_secondCompound_inv_first_entry_order a]
    at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  push_cast at hint
  omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
