-- Prove2me | solution 1 for ThreeSum.BandRawA.incidence_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:44.424684+00:00
-- url     : https://prove2.me/submissions/0ac53e17-ae51-4449-b4bf-55207928d521

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_count_bound
import Theorems.Thm_ThreeSum_BandRawA_items_length_le
import Theorems.Thm_ThreeSum_BandCandidateRows_count_bound


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (items n g (records A B C)).length ≤ 3*m^2*g := by
  have hc := BandCandidateRows.count_bound hA hB hC
  have hi := items_length_le n g (records A B C)
  nlinarith
end ThreeSum.BandRawA
