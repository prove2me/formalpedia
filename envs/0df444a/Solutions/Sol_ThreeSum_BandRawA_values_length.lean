-- Prove2me | solution 1 for ThreeSum.BandRawA.values_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:32.33821+00:00
-- url     : https://prove2.me/submissions/509eae8c-b46f-473d-bee1-1ac30f9df1b7

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (f : ℕ → ℤ) (ls : List Label) : (values f ls).length=ls.length := List.length_map ..
end ThreeSum.BandRawA
