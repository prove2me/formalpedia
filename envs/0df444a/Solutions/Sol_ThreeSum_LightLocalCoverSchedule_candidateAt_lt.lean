-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.candidateAt_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:27.273198+00:00
-- url     : https://prove2.me/submissions/5be49b2e-d060-49ac-bf7c-d58851e8cbd5

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_length
import Definitions.Def_WeightedCache3SUM_Alias_2a51a2d5fba73da5

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
theorem _root_.solution (h : ℕ) (s : Occurrence h) : candidateAt h s < rows h := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact indices_lt h (List.getElem_mem hs)
end ThreeSum.LightLocalCoverSchedule
