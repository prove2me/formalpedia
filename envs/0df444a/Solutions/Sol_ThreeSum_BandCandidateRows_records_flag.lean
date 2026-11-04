-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.records_flag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:00:06.931263+00:00
-- url     : https://prove2.me/submissions/88e637fc-2593-468d-a2da-fb103030f98a

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_WeightedCache3SUM_Alias_ad326dab22673a81
import Theorems.Thm_ThreeSum_BandCandidateRows_make_flag


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    r.flag=0 ∨ r.flag=1 := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩ <;> exact make_flag _ _ _ _
end ThreeSum.BandCandidateRows
