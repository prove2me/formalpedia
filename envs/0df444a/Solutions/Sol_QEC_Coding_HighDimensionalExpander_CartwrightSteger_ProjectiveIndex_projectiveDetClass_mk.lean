-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.projectiveDetClass_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:37:26.168258+00:00
-- url     : https://prove2.me/submissions/d258f410-f0b7-4136-bf7e-5e652b205b3d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
omit [Nonempty n]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution
    (g : Matrix.GeneralLinearGroup n K) :
    projectiveDetClass n K (Matrix.ProjGenLinGroup.mk g) =
      QuotientGroup.mk' _ (Matrix.GeneralLinearGroup.det g) :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
