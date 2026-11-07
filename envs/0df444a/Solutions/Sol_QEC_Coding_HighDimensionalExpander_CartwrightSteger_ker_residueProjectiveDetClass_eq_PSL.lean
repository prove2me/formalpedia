-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ker_residueProjectiveDetClass_eq_PSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:39:50.591165+00:00
-- url     : https://prove2.me/submissions/ac413029-41d6-4a05-996a-51835bd23f87

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_ker_projectiveDetClass_eq_projectiveSpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueProjectiveDetClass P r level).ker = PSL P r level := by
  simpa [residueProjectiveDetClass, PSL, specialToProjective,
    ProjectiveIndex.projectiveSpecialLinear, ResiduePowerClass,
    IndexSelection.PowerClass, IndexSelection.dthPowerUnits,
    ProjectiveIndex.DetPowerClass,
    Fintype.card_fin] using
    (ProjectiveIndex.ker_projectiveDetClass_eq_projectiveSpecialLinear
      (Fin r.matrixRank) (ResidueField P r level))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
