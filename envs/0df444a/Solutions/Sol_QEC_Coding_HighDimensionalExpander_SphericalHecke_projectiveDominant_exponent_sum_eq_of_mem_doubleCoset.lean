-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:49.283829+00:00
-- url     : https://prove2.me/submissions/0633580d-71f6-4f60-93d2-2cc6cf4753db

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinear_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_det_localUnitOrder
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
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by
  obtain ⟨left, right, c, hc, hGL⟩ :=
    scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset k a b hmem
  have hdet := congrArg Matrix.GeneralLinearGroup.det hGL
  have horder := congrArg localUnitOrder hdet
  simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    localUnitOrder_mul, localUnitOrder_pow, hc,
    integralGeneralLinear_det_localUnitOrder_eq_zero,
    dominantGeneralLinear_det_localUnitOrder] using horder
end QEC.Coding.HighDimensionalExpander.SphericalHecke
