-- Prove2me | solution 1 for ThreeSum.LightTernaryMetadata.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:39.206557+00:00
-- url     : https://prove2.me/submissions/bd1a019b-b13e-48c0-a715-055f7bd87ade

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryMetadata
theorem _root_.solution (W n : ℕ) : time W n ≤ 1000*(W+1)*(n+1) := by
  unfold time roundTime LightTernaryCodes.zeroTime LightTernaryCodes.digitTime
    LightMaskErase.time
  nlinarith
end ThreeSum.LightTernaryMetadata
