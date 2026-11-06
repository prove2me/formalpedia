-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.evenGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:10.996599+00:00
-- url     : https://prove2.me/submissions/846b5d20-fcd2-44c1-90a2-02edd764de51

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution : evenGenus 0 = 1063393 := by
  norm_num [evenGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
