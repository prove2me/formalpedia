-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_inv_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:13.089979+00:00
-- url     : https://prove2.me/submissions/6d71ce4c-07c9-46f3-8204-8ee9d9aec01e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_eq_iff_upperRight
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
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g⁻¹ ↔
      UpperRightResidueZero k d r g := by
  have hforward := residueFundamentalPlane_eq_iff_upperRight k d r hr 1 g
  have hbackward := residueFundamentalPlane_eq_iff_upperRight k d r hr g 1
  constructor
  · intro hg
    have heq := hforward.mpr (by simpa using hg)
    have hout := hbackward.mp heq.symm
    simpa using hout
  · intro hg
    have heq := hbackward.mpr (by simpa using hg)
    have hout := hforward.mp heq.symm
    simpa using hout
end QEC.Coding.HighDimensionalExpander.SphericalHecke
