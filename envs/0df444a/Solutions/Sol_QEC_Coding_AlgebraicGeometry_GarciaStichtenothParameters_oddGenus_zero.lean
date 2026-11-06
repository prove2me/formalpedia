-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:01.639391+00:00
-- url     : https://prove2.me/submissions/9e9f7bb3-4ea2-4823-b73c-c23f6c45e171

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : oddGenus 0 = 32705 := by
  norm_num [oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
