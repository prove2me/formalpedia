-- Prove2me | solution 1 for ThreeSum.BandRawA.items_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:46.938184+00:00
-- url     : https://prove2.me/submissions/bb462533-ccf2-4aff-ba3d-2571749fa858

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_WeightedCache3SUM_Alias_f3602a17918e9270

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    labelAt n g rs (count n g rs s+j)=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := firstRows_getD hs hj
end ThreeSum.BandRawA
