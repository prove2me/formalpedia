-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_orderLowerBound_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:47:38.404898+00:00
-- url     : https://prove2.me/submissions/8fba83cc-0ed2-45aa-9247-f6cecf10150e

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
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    MatrixOrderLowerBound
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      (((dominantGeneralLinear k weight.toDominant)⁻¹ :
          GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
  change MatrixOrderLowerBound _
    (diagonalGeneralLinear (LocalFunctionField k) (n + 1)
      (fun i ↦ (uniformizerUnit k ^
        weight.toDominant.exponent i)⁻¹) :
      Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k))
  intro i j
  rw [diagonalGeneralLinear_apply]
  split
  · subst j
    rw [orderTop_uniformizerUnit_pow_inv]
    exact WithTop.coe_le_coe.mpr (neg_le_neg
      (Int.ofNat_le.mpr
        (weight.toDominant.antitone_exponent (Fin.zero_le i))))
  · simp [HahnSeries.orderTop_zero]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
