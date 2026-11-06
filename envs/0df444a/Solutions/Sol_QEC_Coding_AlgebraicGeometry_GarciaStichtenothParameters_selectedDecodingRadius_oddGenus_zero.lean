-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDecodingRadius_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:25.798973+00:00
-- url     : https://prove2.me/submissions/d26614c2-4c8a-4099-8910-2ff04526fbcc

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : selectedDecodingRadius (oddGenus 0) = 4088 := by
  norm_num [selectedDecodingRadius, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
