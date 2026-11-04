-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.mem_records_owner_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:39.593322+00:00
-- url     : https://prove2.me/submissions/1037f239-0a51-4359-900b-b065c4e24118

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory

set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    ∃ o : Owner A B C, fromOwner A B C o=r := by
  rcases List.mem_append.mp hr with hb | hh
  · obtain ⟨j,hj,hk⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
    exact ⟨.inl (⟨j,List.mem_range.mp hj⟩,⟨k,List.mem_range.mp hk⟩),he⟩
  · rcases List.mem_append.mp hh with hb | hc
    · obtain ⟨i,hi,hj⟩ := List.mem_flatMap.mp hb
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hj
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inl ⟨j,List.mem_range.mp hj⟩),he⟩
    · obtain ⟨i,hi,hk⟩ := List.mem_flatMap.mp hc
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inr ⟨k,List.mem_range.mp hk⟩),he⟩
end ThreeSum.BandCandidateRows
