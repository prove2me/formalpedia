-- Prove2me | solution 1 for ThreeSum.BandRawA.ownerLabels_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:53.030414+00:00
-- url     : https://prove2.me/submissions/6057c3bc-7c3c-4810-b36d-61e09b663205

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (ls : List Label) : (ownerLabels ls).length=ls.length := List.length_map ..
end ThreeSum.BandRawA
