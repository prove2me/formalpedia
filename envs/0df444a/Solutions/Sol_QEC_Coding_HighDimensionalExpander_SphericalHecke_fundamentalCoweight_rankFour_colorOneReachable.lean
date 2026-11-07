-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_colorOneReachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:43:59.453165+00:00
-- url     : https://prove2.me/submissions/e187c919-fac7-4b10-8056-5420926dfb84

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_zero_eq_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerProduct_colorOneReachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_rankFour_zero_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_rankFour_zero_one_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (color : Fin 3) :
    ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (fundamentalCoweight k 4 (color.val + 1))) := by
  fin_cases color
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 1))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    have hzero : coordinateUniformizerCoweight k 4 (0 : Fin 4) =
        fundamentalCoweight k 4 1 :=
      coordinateUniformizerCoweight_zero_eq_fundamental k (by decide)
    rw [hzero] at h
    exact h
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 2))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0, 1] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    simpa [coordinateUniformizerCoweight_rankFour_zero_one] using h
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 3))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0, 1, 2] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    rw [← mul_assoc,
      coordinateUniformizerCoweight_rankFour_zero_one_two] at h
    exact h
end QEC.Coding.HighDimensionalExpander.SphericalHecke
