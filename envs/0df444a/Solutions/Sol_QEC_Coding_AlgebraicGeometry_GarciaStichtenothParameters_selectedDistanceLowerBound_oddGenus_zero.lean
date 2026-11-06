-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDistanceLowerBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:30.381085+00:00
-- url     : https://prove2.me/submissions/cb87f862-975f-4acd-963b-20813a39125a

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedDistanceLowerBound (oddGenus 0) = 40883 := by
  norm_num [selectedDistanceLowerBound, selectedDivisorDegree,
    selectedLogicalCount, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
