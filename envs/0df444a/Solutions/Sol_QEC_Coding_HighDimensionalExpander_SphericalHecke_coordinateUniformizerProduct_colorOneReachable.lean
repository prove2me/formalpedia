-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerProduct_colorOneReachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:42:26.008757+00:00
-- url     : https://prove2.me/submissions/f1c7f6fb-0182-4de7-94c4-32d691d45c04

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_smul
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
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (coordinates : List (Fin d)) :
    ColorOneReachable k d (QuotientGroup.mk 1)
      (QuotientGroup.mk
        ((coordinates.map (coordinateUniformizerCoweight k d)).prod)) := by
  induction coordinates with
  | nil =>
      simpa using (Relation.ReflTransGen.refl :
        ColorOneReachable k d (QuotientGroup.mk 1) (QuotientGroup.mk 1))
  | cons i coordinates ih =>
      have hstep : ColoredBuildingAdjacent k d 1
          (QuotientGroup.mk 1)
          (QuotientGroup.mk (coordinateUniformizerCoweight k d i)) := by
        rw [coloredBuildingAdjacent_mk_iff]
        simpa using
          coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
            k hd i
      have htail := colorOneReachable_smul k d
        (coordinateUniformizerCoweight k d i) ih
      have htail' : ColorOneReachable k d
          (QuotientGroup.mk (coordinateUniformizerCoweight k d i))
          (QuotientGroup.mk
            (coordinateUniformizerCoweight k d i *
              (coordinates.map
                (coordinateUniformizerCoweight k d)).prod)) := by
        simpa [MulAction.Quotient.smul_mk, smul_eq_mul] using htail
      exact (Relation.ReflTransGen.single hstep).trans (by
        simpa using htail')
end QEC.Coding.HighDimensionalExpander.SphericalHecke
