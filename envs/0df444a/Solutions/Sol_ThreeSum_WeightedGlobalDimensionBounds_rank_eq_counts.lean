-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.rank_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:48:45.291977+00:00
-- url     : https://prove2.me/submissions/4d75a297-a0ad-4508-92da-600fbb8452f3

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedSchedule_rank_counts


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {N : ℕ} (Q : TritWord N) : rank Q=digitCount Q 1+2*digitCount Q 2 :=
  WeightedSchedule.rank_counts Q
end ThreeSum.WeightedGlobalDimensionBounds
