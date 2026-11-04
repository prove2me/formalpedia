-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:36.726364+00:00
-- url     : https://prove2.me/submissions/0a884314-c333-4672-a214-65067b355836

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (C c d : ℕ) : 0 < scale C c d := by unfold scale; positivity
end ThreeSum.WeightedGlobalCoverScale
