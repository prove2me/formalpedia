-- Prove2me | solution 1 for ThreeSum.BandRawA.positionLabels_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:54.449497+00:00
-- url     : https://prove2.me/submissions/cbbc6057-a554-4652-8b82-3524c69511f0

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (ls : List Label) : (positionLabels ls).length=ls.length := List.length_map ..
end ThreeSum.BandRawA
