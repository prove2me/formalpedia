-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.records_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:28.476903+00:00
-- url     : https://prove2.me/submissions/f0f3ce36-e1fa-4c70-bf81-68465533305c

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_WeightedCache3SUM_Alias_ad326dab22673a81
import Definitions.Def_WeightedCache3SUM_Alias_97307e10b6612548


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution {A B C : Family} {r : Record}
    (hr : r ∈ records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  exact fromOwner_sound A B C o hf
end ThreeSum.BandCandidateRows
