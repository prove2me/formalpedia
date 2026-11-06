-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceUpperBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:15.062205+00:00
-- url     : https://prove2.me/submissions/775c4cd3-3509-412a-8e82-2099c0b40ada

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedEvaluationPlaceUpperBound (oddGenus 0) = 1005676 := by
  norm_num [selectedEvaluationPlaceUpperBound, selectedPlaceCount, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
