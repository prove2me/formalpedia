-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedPhysicalLengthLowerBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:37.35075+00:00
-- url     : https://prove2.me/submissions/e8d439eb-9d37-43eb-a9df-f3fb67944675

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedPhysicalLengthLowerBound (oddGenus 0) = 932089 := by
  norm_num [selectedPhysicalLengthLowerBound, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
