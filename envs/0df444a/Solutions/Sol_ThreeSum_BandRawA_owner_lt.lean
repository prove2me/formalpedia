-- Prove2me | solution 1 for ThreeSum.BandRawA.owner_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:40.605393+00:00
-- url     : https://prove2.me/submissions/60e8614e-5b90-4ef1-b7dd-421fd4cdc062

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_mem_firstRows

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ items n g rs) : l.owner < rs.length := (mem_firstRows.mp hl).1
end ThreeSum.BandRawA
