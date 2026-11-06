-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedPhysicalLengthUpperBound_oddGenus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:44:53.025443+00:00
-- url     : https://prove2.me/submissions/860b5c73-7763-4cb0-b388-8f3bdba03259

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
theorem _root_.solution :
    selectedPhysicalLengthUpperBound (oddGenus 0) = 964796 := by
  norm_num [selectedPhysicalLengthUpperBound, oddGenus]
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
