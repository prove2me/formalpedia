-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:11.138338+00:00
-- url     : https://prove2.me/submissions/7efeadd8-b661-4835-bc78-f5cde1c39123

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyThree
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalNeighborAdjacentEquiv_apply_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_comp_single_apply
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


attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyThree
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalNeighborAdjacentEquiv_apply_val

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (n r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k (n + 1) r)⁻¹ =
      fundamentalDoubleCoset k (n + 1) r')
    (hsset : (fundamentalDoubleCoset k (n + 1) s)⁻¹ =
      fundamentalDoubleCoset k (n + 1) s') :
    buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset =
      buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset := by
  classical
  let Ar := buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset
  let As := buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset
  apply lp.ext_continuousLinearMap (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
    (p := (2 : ℝ≥0∞)) (by norm_num)
  intro z
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext x
  have hsingle : lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
      2 z c = c • buildingVertexDelta k (n + 1) z := by
    simpa [buildingVertexDelta] using
      (lp.single_smul (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
        2 z c (1 : ℂ))
  change ((Ar ∘L As)
      (lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ) 2 z c)) x =
    ((As ∘L Ar)
      (lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ) 2 z c)) x
  rw [hsingle]
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply]
  congr 1
  rw [buildingColoredAdjacencyOperatorOfInv_comp_single_apply
      k (n + 1) r r' s s' hrset hsset z x,
    buildingColoredAdjacencyOperatorOfInv_comp_single_apply
      k (n + 1) s s' r r' hsset hrset z x,
    mul_comm]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
