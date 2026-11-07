-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerClassGenerator_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:12.618937+00:00
-- url     : https://prove2.me/submissions/2c2cffcf-1446-4c4a-898d-7d14a72182dd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_lt_natCard_constantProjectiveClass
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    indexCartwrightStegerClassGenerator P r level u ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨v, huv⟩ := exists_ne u
  intro hu
  have hb : indexB P r level = 1 := by
    have h := congrArg
      (fun g : PGL P r level =>
        (Matrix.ProjGenLinGroup.mk (indexConstantGL P r level
          (constantClassRepresentative P r u)))⁻¹ * g *
            Matrix.ProjGenLinGroup.mk (indexConstantGL P r level
              (constantClassRepresentative P r u))) hu
    simpa [indexCartwrightStegerClassGenerator,
      indexCartwrightStegerGenerator_eq_conj, mul_assoc] using h
  have hv : indexCartwrightStegerClassGenerator P r level v = 1 := by
    simp [indexCartwrightStegerClassGenerator,
      indexCartwrightStegerGenerator_eq_conj, hb]
  exact huv ((indexCartwrightStegerClassGenerator_injective P r level)
    (hu.trans hv.symm)).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
