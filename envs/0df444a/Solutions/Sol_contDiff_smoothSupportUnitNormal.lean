-- Prove2me | solution 1 for contDiff_smoothSupportUnitNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:06.377347+00:00
-- url     : https://prove2.me/submissions/50c5ee9c-4903-4a16-9c48-a794e3ef3d6d

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution :
    ContDiff ℝ ∞ smoothSupportUnitNormal := by
  exact contDiff_circleMap 0 1
