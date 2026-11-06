-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedLogicalCount_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:14.884822+00:00
-- url     : https://prove2.me/submissions/f9427919-519d-4ec5-92ae-060c790af6d6

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : selectedLogicalCount (oddGenus 0) = 40881 := by
  norm_num [selectedLogicalCount, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
