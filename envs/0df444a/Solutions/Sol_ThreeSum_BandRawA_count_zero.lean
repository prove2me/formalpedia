-- Prove2me | solution 1 for ThreeSum.BandRawA.count_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:04.418829+00:00
-- url     : https://prove2.me/submissions/ce19eca7-8b4d-48b5-9b4b-14da3412fa10

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl
end ThreeSum.BandRawA
