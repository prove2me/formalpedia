-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_eq_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:15:52.445781+00:00
-- url     : https://prove2.me/submissions/196d4633-456a-41d5-8a83-25280b5ecb14

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
open QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    star (fundamentalHeckeFunction k d r) =
      fundamentalHeckeFunction k d s := by
  ext x
  have hmem : x⁻¹ ∈ fundamentalDoubleCoset k d r ↔
      x ∈ fundamentalDoubleCoset k d s := by
    rw [← hset]
    simp
  simp only [star_apply, fundamentalHeckeFunction_apply]
  by_cases hx : x⁻¹ ∈ fundamentalDoubleCoset k d r
  · have hx' := hmem.1 hx
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · have hx' : x ∉ fundamentalDoubleCoset k d s :=
      fun hxs ↦ hx (hmem.2 hxs)
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
end QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
