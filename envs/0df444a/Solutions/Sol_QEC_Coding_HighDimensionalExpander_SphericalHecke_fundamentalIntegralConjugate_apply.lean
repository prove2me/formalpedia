-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:27.74098+00:00
-- url     : https://prove2.me/submissions/dabec79e-362a-429f-a0af-9ba1c9751d3a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) (i j : Fin d) :
    fundamentalIntegralConjugate k d r g i j =
      (if i.val < r then ((uniformizerUnit k)⁻¹ : LocalFunctionField k) else 1) *
        integerEmbedding k (g i j) *
      (if j.val < r then (uniformizerUnit k : LocalFunctionField k) else 1) := by
  simp [fundamentalIntegralConjugate, fundamentalDiagonal,
    diagonalGeneralLinear_inv, diagonalGeneralLinear_apply,
    fundamentalDiagonalUnits, Matrix.mul_apply]
  split_ifs <;>
    simp [powerSeriesGeneralLinearToLocal, integerEmbedding,
      coe_uniformizerUnit]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
