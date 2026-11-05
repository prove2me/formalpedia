-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.source_rank_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:47.383989+00:00
-- url     : https://prove2.me/submissions/704c6366-3df5-4cda-a883-2f3de47dd526

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
theorem _root_.solution (m : ℕ) : sourceRank m≤2*fixedLength m := by
  unfold sourceRank fixedLength; omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
