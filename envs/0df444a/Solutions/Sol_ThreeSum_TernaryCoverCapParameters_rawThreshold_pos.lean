-- Prove2me | solution 1 for ThreeSum.TernaryCoverCapParameters.rawThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:51.210516+00:00
-- url     : https://prove2.me/submissions/b471014a-c0db-4124-be17-9061a3bf1c21

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound
namespace ThreeSum.TernaryCoverCapParameters
theorem _root_.solution (p B k : ℕ) : 0 < rawThreshold p B k := Nat.pow_pos (by decide)
end ThreeSum.TernaryCoverCapParameters
