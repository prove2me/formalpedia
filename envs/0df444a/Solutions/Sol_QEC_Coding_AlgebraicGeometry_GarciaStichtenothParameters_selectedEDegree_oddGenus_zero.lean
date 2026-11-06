-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEDegree_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:55.394134+00:00
-- url     : https://prove2.me/submissions/eb6be4c4-5133-4eaa-9cf2-0cb452bf1c01

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : selectedEDegree (oddGenus 0) = 8175 := by
  norm_num [selectedEDegree, selectedPlaceCount, selectedDivisorDegree, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
