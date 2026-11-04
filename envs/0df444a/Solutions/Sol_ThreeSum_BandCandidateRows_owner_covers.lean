-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.owner_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:16.324206+00:00
-- url     : https://prove2.me/submissions/cc52c951-21a2-485b-9210-98e42b9a3699

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandCandidateRows_records_getD_slot
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_of_candidate
import Definitions.Def_WeightedCache3SUM_Alias_463ae85b9bcdc14e


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution (A B C : Family) (t : Triple A B C) (ht : relevant A B C t) :
    (records A B C).getD (slot A B C (owner A B C t)) default=fromTriple t := by
  rw [records_getD_slot]
  exact fromOwner_of_candidate A B C _ t (candidate_owner A B C t ht)
end ThreeSum.BandCandidateRows
