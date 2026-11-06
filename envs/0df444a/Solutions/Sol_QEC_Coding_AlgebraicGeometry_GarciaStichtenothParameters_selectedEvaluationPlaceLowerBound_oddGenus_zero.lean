-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceLowerBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:09.466876+00:00
-- url     : https://prove2.me/submissions/8e04f879-71db-4b67-ab59-307310f3732a

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedEvaluationPlaceLowerBound (oddGenus 0) = 972971 := by
  norm_num [selectedEvaluationPlaceLowerBound, selectedPlaceCount, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
