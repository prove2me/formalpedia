-- Prove2me | solution 1 for ThreeSum.BandRawA.three_lifts_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:41.947956+00:00
-- url     : https://prove2.me/submissions/a4f4c9b1-2f63-449f-9dc7-e9ae627bc963

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_incidence_bound

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    3*(items n g (records A B C)).length ≤ 9*m^2*g := by
  have hh := incidence_bound (n := n) (g := g) hA hB hC
  nlinarith
end ThreeSum.BandRawA
