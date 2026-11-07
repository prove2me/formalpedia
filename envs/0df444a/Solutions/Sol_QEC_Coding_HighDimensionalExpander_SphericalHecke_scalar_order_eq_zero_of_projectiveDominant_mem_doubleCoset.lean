-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:30.202925+00:00
-- url     : https://prove2.me/submissions/80e8ef8c-82e9-48ff-8828-faf7e8da8056

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalarGeneralLinear_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_orderLowerBound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_last_entry_order
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
    ∃ (left right :
        GL (Fin (n + 1)) (Valued.integer (LocalFunctionField k)))
      (c : Units (LocalFunctionField k)),
      localUnitOrder c = 0 ∧
      dominantGeneralLinear k a.toDominant =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c *
          (integralGeneralLinearToLocal k (n + 1) left *
            dominantGeneralLinear k b.toDominant *
            integralGeneralLinearToLocal k (n + 1) right) := by
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset] at hmem
  rcases hmem with ⟨y, hy, rightP, hrightP, hproduct⟩
  rcases hy with ⟨leftP, hleftP, diagonal, hdiagonal, hyproduct⟩
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  change leftP ∈ maximalCompact k (n + 1) at hleftP
  change rightP ∈ maximalCompact k (n + 1) at hrightP
  rw [mem_maximalCompact_iff] at hleftP hrightP
  obtain ⟨left, hleft⟩ := hleftP
  obtain ⟨right, hright⟩ := hrightP
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) left) = leftP at hleft
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) right) = rightP at hright
  have hprojective :
      Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k a.toDominant) =
        Matrix.ProjGenLinGroup.mk
          (integralGeneralLinearToLocal k (n + 1) left *
            dominantGeneralLinear k b.toDominant *
            integralGeneralLinearToLocal k (n + 1) right) := by
    change dominantCoweight k a.toDominant = _
    rw [map_mul, map_mul, hleft, hright]
    rw [← hyproduct] at hproduct
    exact hproduct.symm
  obtain ⟨c, hGL⟩ :=
    exists_scalar_mul_eq_of_projective_mk_eq hprojective
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalar := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hleftBound : MatrixOrderLowerBound 0
      (leftLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound left
  have hrightBound : MatrixOrderLowerBound 0
      (rightLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound right
  have hdiagonalABound : MatrixOrderLowerBound 0
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero a.toDominant
  have hdiagonalBBound : MatrixOrderLowerBound 0
      (diagonalB : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero b.toDominant
  have hscalarBound : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (scalar : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    scalarGeneralLinear_orderLowerBound c
  have hrightProductBound : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (scalar * (leftLocal * diagonalB * rightLocal) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using hscalarBound.mul
      ((hleftBound.mul hdiagonalBBound).mul hrightBound)
  have hmatrix :
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) =
      (scalar * (leftLocal * diagonalB * rightLocal) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    congrArg Units.val hGL
  have hdiagonalALowerC : MatrixOrderLowerBound
      (localUnitOrder c : WithTop ℤ)
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) := by
    rw [hmatrix]
    exact hrightProductBound
  have hc_le : localUnitOrder c ≤ 0 := by
    have h := hdiagonalALowerC (Fin.last n) (Fin.last n)
    rw [projectiveDominant_last_entry_order a] at h
    exact WithTop.coe_le_coe.mp h
  have hleftInvBound : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hrightInvBound : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hscalarInvBound : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      ((scalar⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [show scalar⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c⁻¹ by
        exact (map_inv _ c).symm]
    simpa [localUnitOrder_inv] using
      (scalarGeneralLinear_orderLowerBound (d := n + 1) c⁻¹)
  have hreverse :
      diagonalB = leftLocal⁻¹ * scalar⁻¹ * diagonalA * rightLocal⁻¹ := by
    dsimp [diagonalA, diagonalB, leftLocal, rightLocal, scalar] at hGL ⊢
    rw [hGL]
    group
  have hreverseProductBound : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      (leftLocal⁻¹ * scalar⁻¹ * diagonalA * rightLocal⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa using
      (((hleftInvBound.mul hscalarInvBound).mul hdiagonalABound).mul
        hrightInvBound)
  have hdiagonalBLowerNegC : MatrixOrderLowerBound
      ((-localUnitOrder c : ℤ) : WithTop ℤ)
      (diagonalB : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) := by
    rw [hreverse]
    exact hreverseProductBound
  have hnegc_le : -localUnitOrder c ≤ 0 := by
    have h := hdiagonalBLowerNegC (Fin.last n) (Fin.last n)
    rw [projectiveDominant_last_entry_order b] at h
    exact WithTop.coe_le_coe.mp h
  refine ⟨left, right, c, ?_, hGL⟩
  omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
