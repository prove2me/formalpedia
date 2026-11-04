-- Prove2me | solution 1 for ThreeSum.BandRawA.firstRows_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:03.294343+00:00
-- url     : https://prove2.me/submissions/965dbfe6-a4b6-46b8-babb-0eef7809ba98

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) : firstRows n g rs 0=[] := rfl
end ThreeSum.BandRawA
