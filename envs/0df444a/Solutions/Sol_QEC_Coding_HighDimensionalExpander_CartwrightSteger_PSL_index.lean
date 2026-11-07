-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:47.708197+00:00
-- url     : https://prove2.me/submissions/baeaf98e-5630-482c-85ff-94687ab63002

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_index_projectiveSpecialLinear
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
    (PSL P r level).index =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank := by
  calc
    (PSL P r level).index =
        Nat.card (ResiduePowerClass P r level) := by
      simpa [PSL, specialToProjective,
        ProjectiveIndex.projectiveSpecialLinear, ResiduePowerClass,
        IndexSelection.PowerClass, IndexSelection.dthPowerUnits,
        ProjectiveIndex.DetPowerClass,
        Fintype.card_fin] using
        (ProjectiveIndex.index_projectiveSpecialLinear
          (Fin r.matrixRank) (ResidueField P r level))
    _ = (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank :=
      by
        simpa only [ResiduePowerClass, Fintype.card_fin] using
          (IndexSelection.natCard_powerClass
            (ResidueField P r level) (Fintype.card (Fin r.matrixRank)))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
