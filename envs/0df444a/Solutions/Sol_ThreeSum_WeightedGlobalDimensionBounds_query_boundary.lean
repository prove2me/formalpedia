-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.query_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:55:25.523483+00:00
-- url     : https://prove2.me/submissions/c3a4311b-f873-4d96-9b3a-c29946697cfc

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_cut_schedule
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
import Theorems.Thm_ThreeSum_WeightedSchedule_query_boundary


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : cacheCost Q+1024-bankCut m j=queryDeficit m j := by
  rw [cut_schedule,deficit_schedule]
  exact WeightedSchedule.query_boundary hQ
end ThreeSum.WeightedGlobalDimensionBounds
