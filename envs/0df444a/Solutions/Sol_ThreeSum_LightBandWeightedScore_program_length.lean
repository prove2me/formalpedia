-- Prove2me | solution 1 for ThreeSum.LightBandWeightedScore.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:08.279553+00:00
-- url     : https://prove2.me/submissions/2573305e-3e75-4ed3-92f0-5276d5aa9f39

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScore
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandWeightedScore
theorem _root_.solution : program.length=17 := rfl
end ThreeSum.LightBandWeightedScore
