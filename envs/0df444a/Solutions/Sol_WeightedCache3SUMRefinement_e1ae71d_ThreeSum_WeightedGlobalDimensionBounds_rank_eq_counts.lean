-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds.rank_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:03:31.313502+00:00
-- url     : https://prove2.me/submissions/a8b92170-db1e-4349-81d4-10098ac3c0ca

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_rank_counts


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {N : ℕ} (Q : TritWord N) : rank Q=digitCount Q 1+2*digitCount Q 2 :=
  WeightedSchedule.rank_counts Q
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
