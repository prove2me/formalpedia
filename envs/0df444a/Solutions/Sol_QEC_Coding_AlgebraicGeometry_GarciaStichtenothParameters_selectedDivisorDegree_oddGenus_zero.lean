-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDivisorDegree_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:14.086612+00:00
-- url     : https://prove2.me/submissions/31f13ebd-b6e1-41c8-8d43-b6db2934bc75

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : selectedDivisorDegree (oddGenus 0) = 147172 := by
  norm_num [selectedDivisorDegree, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
