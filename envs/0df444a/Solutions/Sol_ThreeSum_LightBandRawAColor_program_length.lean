-- Prove2me | solution 1 for ThreeSum.LightBandRawAColor.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:21.615668+00:00
-- url     : https://prove2.me/submissions/91617d60-2e7f-4dfd-ba45-e0e87a1fa42d

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBandRawAColor
theorem _root_.solution : program.length=44 := rfl
end ThreeSum.LightBandRawAColor
