-- Prove2me | solution 1 for ThreeSum.LightSourceBandPair.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:32:35.177699+00:00
-- url     : https://prove2.me/submissions/4ef34cfc-e41f-4b80-affd-87039ba75eb5

import Definitions.Def_Submission_ThreeSum_LightSourceBandProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightSourceBandPair

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandPair
open Light BandPartition SourceBandPairData
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandPair
theorem _root_.solution : program.length=14 := rfl
end ThreeSum.LightSourceBandPair
