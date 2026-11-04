-- Prove2me | solution 1 for ThreeSum.BandRawA.items_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:08.692892+00:00
-- url     : https://prove2.me/submissions/a144a26e-78f1-4721-b359-95a1e48866bd

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_firstRows_index

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    ∃ s < rs.length, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := firstRows_index hk
end ThreeSum.BandRawA
