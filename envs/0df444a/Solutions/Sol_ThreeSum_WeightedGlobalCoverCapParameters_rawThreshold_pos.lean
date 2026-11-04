-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverCapParameters.rawThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:43.621883+00:00
-- url     : https://prove2.me/submissions/36d22c35-8daa-4da6-8d90-bc1c4a18bb3c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
namespace ThreeSum.WeightedGlobalCoverCapParameters
theorem _root_.solution (p B k : ℕ) : 0 < rawThreshold p B k := Nat.pow_pos (by decide)
end ThreeSum.WeightedGlobalCoverCapParameters
