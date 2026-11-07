-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToInteger_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:46.733201+00:00
-- url     : https://prove2.me/submissions/fc2fcce4-37d9-4481-aee9-41943e6e92ce

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
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    powerSeriesGeneralLinearToInteger k d
        (integerGeneralLinearToPowerSeries k d g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [powerSeriesGeneralLinearToInteger,
    integerGeneralLinearToPowerSeries]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
