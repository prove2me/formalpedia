-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:38:49.004587+00:00
-- url     : https://prove2.me/submissions/de2cd9fa-632a-4b67-b7ad-9d961c883816

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_projectiveDetClass_mk
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generalLinear_det_surjective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution :
    Function.Surjective (projectiveDetClass n K) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro u
  obtain ⟨A, hA⟩ := generalLinear_det_surjective n K u
  refine ⟨Matrix.ProjGenLinGroup.mk A, ?_⟩
  rw [projectiveDetClass_mk, hA]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
