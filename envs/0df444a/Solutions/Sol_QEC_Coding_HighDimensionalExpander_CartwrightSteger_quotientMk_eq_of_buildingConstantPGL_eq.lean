-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_buildingConstantPGL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:31.828429+00:00
-- url     : https://prove2.me/submissions/1711ebb2-4271-43b8-b3b8-81971b56f192

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantMatrix_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstant_conj_frobeniusMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_constantFrobenius_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
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
open scoped MatrixGroups
set_option maxHeartbeats 400000
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : buildingConstantPGLHom P r u = buildingConstantPGLHom P r v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by
  change Matrix.ProjGenLinGroup.mk (buildingConstantGL P r u) =
    Matrix.ProjGenLinGroup.mk (buildingConstantGL P r v) at h
  obtain ⟨a, ha⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq h
  let U := buildingConstantGL P r u
  let V := buildingConstantGL P r v
  let S := Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a
  have hUV : U = S * V := ha
  have hScomm (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M = M * (S : Matrix _ _ _) := by
    dsimp [S]
    exact Matrix.scalar_comm _ (fun b => Commute.all _ b) M
  have hScancel (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) = M := by
    rw [hScomm]
    simp only [mul_assoc]
    rw [← Units.val_mul]
    simp
  have hconj :
      (U : Matrix _ _ _) * buildingFrobeniusMatrix P r *
          ((U⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) =
        (V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
          ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) := by
    rw [hUV]
    calc
      (((S * V : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) *
          buildingFrobeniusMatrix P r *
          (((S * V)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _)) =
        (S : Matrix _ _ _) *
          ((V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
            ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)) *
          ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) := by
              simp only [mul_inv_rev, Units.val_mul]
              group
      _ = _ := by
        let M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P) :=
          (V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
            ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)
        calc
          _ = (S : Matrix _ _ _) * M *
              ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (BuildingLocalField P)) : Matrix _ _ _) := by
                  dsimp [M]
          _ = M := hScancel M
          _ = _ := by dsimp [M]
  have hratioMatrix : buildingConstantMatrix P r
        ((u : ConstantExtension P r) *
          (constantFrobenius P r (u : ConstantExtension P r))⁻¹) =
      buildingConstantMatrix P r
        ((v : ConstantExtension P r) *
          (constantFrobenius P r (v : ConstantExtension P r))⁻¹) := by
    have hprod : buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
          buildingFrobeniusMatrix P r =
        buildingConstantMatrix P r
          ((v : ConstantExtension P r) *
            (constantFrobenius P r (v : ConstantExtension P r))⁻¹) *
          buildingFrobeniusMatrix P r := by
      rw [← buildingConstant_conj_frobeniusMatrix P r u,
        ← buildingConstant_conj_frobeniusMatrix P r v]
      exact hconj
    have hc := congrArg (fun M => M *
      (((buildingFrobeniusGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _)) hprod
    change buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
          ((buildingFrobeniusGL P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (BuildingLocalField P)) : Matrix _ _ _) *
          (((buildingFrobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _) =
      buildingConstantMatrix P r
          ((v : ConstantExtension P r) *
            (constantFrobenius P r (v : ConstantExtension P r))⁻¹) *
          ((buildingFrobeniusGL P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (BuildingLocalField P)) : Matrix _ _ _) *
          (((buildingFrobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _) at hc
    simpa only [mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one] using hc
  have hratio := buildingConstantMatrix_injective P r hratioMatrix
  have hfu : constantFrobenius P r (u : ConstantExtension P r) ≠ 0 := by simp
  have hfv : constantFrobenius P r (v : ConstantExtension P r) ≠ 0 := by simp
  have hcross : (u : ConstantExtension P r) *
      constantFrobenius P r (v : ConstantExtension P r) =
    (v : ConstantExtension P r) *
      constantFrobenius P r (u : ConstantExtension P r) := by
    apply (div_eq_div_iff hfu hfv).mp
    simpa [div_eq_mul_inv] using hratio
  have hfixed : constantFrobenius P r
      ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
    (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hdiv : constantFrobenius P r (u : ConstantExtension P r) /
        constantFrobenius P r (v : ConstantExtension P r) =
      (u : ConstantExtension P r) / (v : ConstantExtension P r) := by
      apply (div_eq_div_iff hfv (Units.ne_zero v)).mpr
      simpa [mul_comm] using hcross.symm
    simpa [map_mul, map_inv, div_eq_mul_inv] using hdiv
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_constantFrobenius_eq P r _ hfixed
  have hc0 : c ≠ 0 := by
    intro hcZero
    rw [hcZero, map_zero] at hc
    exact (mul_ne_zero (Units.ne_zero u) (inv_ne_zero (Units.ne_zero v))) hc.symm
  apply QuotientGroup.eq_iff_div_mem.mpr
  change u / v ∈ baseScalarUnits P r
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa [baseScalarUnitHom, div_eq_mul_inv] using hc
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
