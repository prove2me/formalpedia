-- Prove2me | solution 1 for contDiff_smoothSupportUnitTangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:26.167537+00:00
-- url     : https://prove2.me/submissions/925c6667-dc63-4308-8f5a-21e2c162cc5a

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_contDiff_smoothSupportUnitNormal

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution :
    ContDiff ℝ ∞ smoothSupportUnitTangent := by
  exact contDiff_smoothSupportUnitNormal.mul contDiff_const
