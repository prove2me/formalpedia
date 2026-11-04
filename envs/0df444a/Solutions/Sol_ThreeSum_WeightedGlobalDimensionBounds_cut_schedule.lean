-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.cut_schedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:47:52.043189+00:00
-- url     : https://prove2.me/submissions/ba69ffbb-7d09-4f7e-a4ee-124ae0452c2b

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution (m j : ℕ) : bankCut m j=WeightedSchedule.bankCut (j*m) := by
  unfold bankCut WeightedSchedule.bankCut; ring
end ThreeSum.WeightedGlobalDimensionBounds
