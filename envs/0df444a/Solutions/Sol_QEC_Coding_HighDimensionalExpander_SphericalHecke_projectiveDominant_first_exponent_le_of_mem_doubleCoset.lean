-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_first_exponent_le_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:44.280527+00:00
-- url     : https://prove2.me/submissions/16cb0c7b-67c8-421f-bf66-580e46b3638a

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_orderLowerBound_first
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_first_entry_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
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
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    a.toDominant.exponent (0 : Fin (n + 1)) ≤
      b.toDominant.exponent (0 : Fin (n + 1)) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hdiagonalBInv :=
    projectiveDominant_inv_orderLowerBound_first (k := k) b
  have hscalarInv : MatrixOrderLowerBound 0
      ((scalar⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [show scalar⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c⁻¹ by
        exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv, hc] using
      (scalarGeneralLinear_orderLowerBound (d := n + 1) c⁻¹)
  have hinverse :
      diagonalA⁻¹ =
        rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hproduct : MatrixOrderLowerBound
      ((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      (rightLocal⁻¹ * diagonalB⁻¹ * leftLocal⁻¹ * scalar⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using
      (((hrightInv.mul hdiagonalBInv).mul hleftInv).mul hscalarInv)
  have hboundA : MatrixOrderLowerBound
      ((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      ((diagonalA⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [hinverse]
    exact hproduct
  have hentry := hboundA (0 : Fin (n + 1)) 0
  rw [projectiveDominant_inv_first_entry_order a] at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
