-- Prove2me | solution 1 for ThreeSum.BandRawA.index_lt_items
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:48.155913+00:00
-- url     : https://prove2.me/submissions/702efe6b-e0f1-404f-949e-e37d022f3587

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_index_lt_firstRows

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (items n g rs).length := index_lt_firstRows hs hj
end ThreeSum.BandRawA
