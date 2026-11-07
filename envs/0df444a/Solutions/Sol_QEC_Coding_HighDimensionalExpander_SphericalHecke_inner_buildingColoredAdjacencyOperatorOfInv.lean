-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_buildingColoredAdjacencyOperatorOfInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:54:29.796467+00:00
-- url     : https://prove2.me/submissions/df1da6eb-c5be-4032-b1ba-e922231f27d8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_summable_inner_coloredBuildingEdge_target_source_of_inv
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
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r)
    (f g : BuildingL2 k d) :
    inner ℂ (buildingColoredAdjacencyOperatorOfInv k d r s hset f) g =
      inner ℂ f (buildingColoredAdjacencyOperatorOfInv k d s r hsset g) := by
  let er := coloredBuildingEdgeReverseEquiv k d r s hset
  have hr := summable_inner_coloredBuildingEdge_target_source_of_inv
    k d r s hset f g
  have hs := summable_inner_coloredBuildingEdge_target_source_of_inv
    k d s r hsset g f
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp_rw [buildingColoredAdjacencyOperatorOfInv_apply_apply,
    sum_inner, inner_sum]
  calc
    (∑' x : BuildingVertex k d,
        ∑ y : {y // ColoredBuildingAdjacent k d r x y},
          inner ℂ (f y) (g x)) =
        ∑' e : ColoredBuildingEdge k d r,
          inner ℂ (f e.2.1) (g e.1) := by
      exact (hr.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])).symm
    _ = ∑' e : ColoredBuildingEdge k d s,
          inner ℂ (f e.1) (g e.2.1) := by
      simpa [er, coloredBuildingEdgeReverseEquiv] using
        (er.tsum_eq (fun e : ColoredBuildingEdge k d s ↦
          inner ℂ (f e.1) (g e.2.1)))
    _ = ∑' x : BuildingVertex k d,
        ∑ y : {y // ColoredBuildingAdjacent k d s x y},
          inner ℂ (f x) (g y) := by
      have hs' : Summable (fun e : ColoredBuildingEdge k d s ↦
          inner ℂ (f e.1) (g e.2.1)) := by
        simpa only [inner_conj_symm] using
          (Complex.summable_conj.mpr hs)
      exact hs'.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])
end QEC.Coding.HighDimensionalExpander.SphericalHecke
