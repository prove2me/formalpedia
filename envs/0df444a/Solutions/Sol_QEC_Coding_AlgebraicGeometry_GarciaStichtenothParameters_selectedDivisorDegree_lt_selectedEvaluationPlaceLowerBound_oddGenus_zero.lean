-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDivisorDegree_lt_selectedEvaluationPlaceLowerBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:25.171211+00:00
-- url     : https://prove2.me/submissions/387287a9-3a33-40ca-a9ba-57e7d24074c3

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedDivisorDegree (oddGenus 0) < selectedEvaluationPlaceLowerBound (oddGenus 0) := by
  norm_num [selectedDivisorDegree, selectedEvaluationPlaceLowerBound,
    selectedPlaceCount, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
