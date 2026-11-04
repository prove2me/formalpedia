-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:49:24.176302+00:00
-- url     : https://prove2.me/submissions/63913a4f-90fb-4c3d-be7e-f28b58b409a1

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
theorem _root_.solution (m j : ℕ) : queryDeficit m j=WeightedSchedule.treeBudget (j*m) := by
  unfold queryDeficit WeightedSchedule.treeBudget WeightedSchedule.dropBudget; ring
end ThreeSum.WeightedGlobalDimensionBounds
