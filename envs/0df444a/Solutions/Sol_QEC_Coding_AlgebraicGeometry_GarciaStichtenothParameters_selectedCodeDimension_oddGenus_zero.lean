-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedCodeDimension_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:26.653145+00:00
-- url     : https://prove2.me/submissions/b7ecd486-9a08-4664-ac74-97ce0f76e167

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : selectedCodeDimension (oddGenus 0) = 114468 := by
  norm_num [selectedCodeDimension, selectedDivisorDegree, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
