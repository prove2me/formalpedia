-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.getD_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:01.847283+00:00
-- url     : https://prove2.me/submissions/fba37f71-d9de-4045-b36f-587407ac15b6

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Theorems.Thm_ThreeSum_BandCandidateRows_records_sound

set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution {A B C : Family} {s : ℕ} (hs : s < (records A B C).length)
    (hf : ((records A B C).getD s default).flag=1) :
    let r := (records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  apply records_sound _ hf
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs
end ThreeSum.BandCandidateRows
