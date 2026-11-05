-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds.deficit_schedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:04:26.701587+00:00
-- url     : https://prove2.me/submissions/b882382d-b438-4608-ac93-fcbab33dbf75

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution (m j : ℕ) : queryDeficit m j=WeightedSchedule.treeBudget (j*m) := by
  unfold queryDeficit WeightedSchedule.treeBudget WeightedSchedule.dropBudget; ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
