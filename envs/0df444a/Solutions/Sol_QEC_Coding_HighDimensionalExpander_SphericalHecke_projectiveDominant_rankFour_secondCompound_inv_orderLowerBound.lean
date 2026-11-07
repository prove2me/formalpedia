-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:09.102063+00:00
-- url     : https://prove2.me/submissions/24457a4a-c70b-4933-abce-1722a348c84f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompound_diagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_wedgePair_sum_le_first
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
    {k : Type u} [Field k]
    (weight : ProjectiveDominantCoweight 3) :
    MatrixOrderLowerBound
      ((-((weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear
          (dominantGeneralLinear k weight.toDominant))⁻¹ :
          GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
  rw [rankFourSecondCompoundGeneralLinear_inv_val]
  change MatrixOrderLowerBound _ (rankFourSecondCompound
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))))
  have hdiagInv := congrArg Units.val
    (diagonalGeneralLinear_inv (LocalFunctionField k) 4
      (fun i ↦ uniformizerUnit k ^ weight.toDominant.exponent i))
  change ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin 4) (LocalFunctionField k)) :
      Matrix (Fin 4) (Fin 4) (LocalFunctionField k))) = _ at hdiagInv
  rw [hdiagInv]
  have hdiagVal :
      (diagonalGeneralLinear (LocalFunctionField k) 4
        (fun i ↦ (uniformizerUnit k ^
          weight.toDominant.exponent i)⁻¹) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) =
      Matrix.diagonal (fun i ↦
        (((uniformizerUnit k ^ weight.toDominant.exponent i)⁻¹ :
          Units (LocalFunctionField k)) : LocalFunctionField k)) := by
    apply Matrix.ext
    intro i j
    simp only [diagonalGeneralLinear_apply, Matrix.diagonal_apply]
  rw [hdiagVal, rankFourSecondCompound_diagonal]
  intro p q
  rw [Matrix.diagonal_apply]
  split
  · subst q
    rw [HahnSeries.orderTop_mul,
      orderTop_uniformizerUnit_pow_inv,
      orderTop_uniformizerUnit_pow_inv]
    apply WithTop.coe_le_coe.mpr
    push_cast
    have hp := projectiveDominant_rankFour_wedgePair_sum_le_first weight p
    omega
  · simp [HahnSeries.orderTop_zero]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
