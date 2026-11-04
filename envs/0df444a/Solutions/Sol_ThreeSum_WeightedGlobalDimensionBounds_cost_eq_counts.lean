-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.cost_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:48:42.452085+00:00
-- url     : https://prove2.me/submissions/7c922c2a-0888-4275-a9c6-d3d6eeacaf2a

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedSchedule_cacheCost_counts


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {N : ℕ} (Q : TritWord N) : cacheCost Q=512*digitCount Q 1+1025*digitCount Q 2 :=
  WeightedSchedule.cacheCost_counts Q
end ThreeSum.WeightedGlobalDimensionBounds
