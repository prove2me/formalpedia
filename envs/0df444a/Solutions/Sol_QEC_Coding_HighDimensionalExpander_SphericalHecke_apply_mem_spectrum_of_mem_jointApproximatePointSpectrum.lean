-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:03:35.173171+00:00
-- url     : https://prove2.me/submissions/88c85654-e5db-4d69-ae49-63e528d6860f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_two
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_two

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ)
    (ha : a ∈ jointApproximatePointSpectrum A) (i : ι) :
    a i ∈ spectrum ℂ (A i) := by
  by_contra hspec
  have hunit : IsUnit
      (algebraMap ℂ (E →L[ℂ] E) (a i) - A i) :=
    spectrum.notMem_iff.mp hspec
  obtain ⟨u, hu⟩ := hunit
  let C : ℝ := ‖((↑u⁻¹) : E →L[ℂ] E)‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  obtain ⟨v, hv, hres⟩ := ha C⁻¹ (inv_pos.mpr hC)
  have huApply : ((u : E →L[ℂ] E) v) =
      a i • v - A i v := by
    rw [hu]
    simp [Algebra.algebraMap_eq_smul_one]
  have hresU : ‖(u : E →L[ℂ] E) v‖ < C⁻¹ := by
    rw [huApply, norm_sub_rev]
    exact hres i
  have hvInv : v = ((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
      ((u : E →L[ℂ] E) v) := by
    have hmul := congrArg
      (fun T : E →L[ℂ] E ↦ T v)
      u.inv_mul
    calc
      v = (1 : E →L[ℂ] E) v := by simp
      _ = ((((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) *
          (u : E →L[ℂ] E)) v) := hmul.symm
      _ = ((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
          ((u : E →L[ℂ] E) v) := rfl
  have hnormInv :=
    (((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E).le_opNorm
      ((u : E →L[ℂ] E) v))
  have hprodLt :
      ‖((↑u⁻¹) : E →L[ℂ] E)‖ *
          ‖(u : E →L[ℂ] E) v‖ < 1 := by
    calc
      ‖((↑u⁻¹) : E →L[ℂ] E)‖ *
          ‖(u : E →L[ℂ] E) v‖ ≤
          C * ‖(u : E →L[ℂ] E) v‖ := by
        apply mul_le_mul_of_nonneg_right
        · dsimp only [C]
          linarith
        · exact norm_nonneg _
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left hresU hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have : ‖v‖ < 1 := by
    rw [hvInv]
    exact hnormInv.trans_lt hprodLt
  rw [hv] at this
  exact (lt_irrefl 1 this)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
