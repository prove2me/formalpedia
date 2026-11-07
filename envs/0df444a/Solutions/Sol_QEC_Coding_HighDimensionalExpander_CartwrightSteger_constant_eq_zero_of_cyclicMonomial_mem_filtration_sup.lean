-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constant_eq_zero_of_cyclicMonomial_mem_filtration_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:37:04.834086+00:00
-- url     : https://prove2.me/submissions/b592836b-503d-47ad-ad93-67f8a8cc0147

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constant_eq_zero_of_eq_infinityUniformizer_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_infinityUniformizerMultiple_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_eq_zero_of_mem_filtration
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
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
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : Fin r.matrixRank)
    (hmem : constantMatrix P r c * cyclicGeneratorMatrix P r ^ (k : ℕ) ∈
      InfinityCyclicFiltration P r (k : ℕ) ⊔
        InfinityUniformizerMultiple P r) :
    c = 0 := by
  rw [Submodule.mem_sup] at hmem
  obtain ⟨A, hA, B, hB, hAB⟩ := hmem
  obtain ⟨Y, hYL, hBY⟩ :=
    (mem_infinityUniformizerMultiple_iff P r B).mp hB
  let YL : InfinityCyclicLattice P r := ⟨Y, hYL⟩
  apply (constantBasis P r).repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  let p : Fin r.matrixRank × Fin r.matrixRank := (i, k)
  have hAcoord : (splittingCyclicBasis P r).repr A p = 0 :=
    splittingCyclicBasis_repr_eq_zero_of_mem_filtration
      P r (k : ℕ) A hA p (by simp [p])
  have hAcoord' : (splittingCyclicBasis P r).coord p A = 0 := by
    simpa only [Module.Basis.coord_apply] using hAcoord
  have hcoord :
      (splittingCyclicBasis P r).coord p
          (constantMatrix P r c * cyclicGeneratorMatrix P r ^ (k : ℕ)) =
        (splittingCyclicBasis P r).coord p B := by
    calc
      _ = (splittingCyclicBasis P r).coord p (A + B) := by rw [hAB]
      _ = (splittingCyclicBasis P r).coord p A +
          (splittingCyclicBasis P r).coord p B := by rw [map_add]
      _ = _ := by rw [hAcoord', zero_add]
  have hXcoord : (splittingCyclicBasis P r).coord p
      (constantMatrix P r c * cyclicGeneratorMatrix P r ^ (k : ℕ)) =
      algebraMap (BaseField P) (SplittingFunctionField P r)
        ((constantBasis P r).repr c i) := by
    simpa only [Module.Basis.coord_apply, p, ↓reduceIte] using
      splittingCyclicBasis_repr_cyclicMonomial P r c k p
  rw [hXcoord] at hcoord
  rw [hBY] at hcoord
  change _ = (splittingCyclicBasis P r).coord p
      ((infinityUniformizer P r : SplittingFunctionField P r) • Y) at hcoord
  rw [map_smul] at hcoord
  have hYcoord : (splittingCyclicBasis P r).coord p Y =
      algebraMap (InfinityCoefficientRing P r)
        (SplittingFunctionField P r) ((infinityCyclicBasis P r).repr YL p) := by
    simpa only [Module.Basis.coord_apply] using
      splittingCyclicBasis_repr_coe P r YL p
  rw [hYcoord] at hcoord
  change _ = (infinityUniformizer P r : SplittingFunctionField P r) *
      algebraMap (InfinityCoefficientRing P r)
        (SplittingFunctionField P r) ((infinityCyclicBasis P r).repr YL p) at hcoord
  have hz := constant_eq_zero_of_eq_infinityUniformizer_mul P r
    (algebraMap (BaseField P) (ConstantExtension P r)
      ((constantBasis P r).repr c i))
    ((infinityCyclicBasis P r).repr YL p) (by
      change (algebraMap (ConstantExtension P r) (SplittingFunctionField P r))
          ((algebraMap (BaseField P) (ConstantExtension P r))
            ((constantBasis P r).repr c i)) = _
      rw [← IsScalarTower.algebraMap_apply]
      exact hcoord)
  exact (algebraMap (BaseField P) (ConstantExtension P r)).injective
    (by simpa using hz)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
