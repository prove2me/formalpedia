-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:51.703821+00:00
-- url     : https://prove2.me/submissions/302f6748-a766-49a0-abc2-4efb7a164b7f

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (C c d : ℕ) : 0 < scale C c d := by unfold scale; positivity
end ThreeSum.TernaryCoverScale
