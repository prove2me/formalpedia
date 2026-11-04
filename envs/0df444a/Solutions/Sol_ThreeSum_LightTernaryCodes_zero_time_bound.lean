-- Prove2me | solution 1 for ThreeSum.LightTernaryCodes.zero_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:33.073334+00:00
-- url     : https://prove2.me/submissions/aa6d4a70-fac0-4e16-be57-e5d32e602ce8

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryCodes
theorem _root_.solution (W : ℕ) : zeroTime W ≤ 400*(W+1) := by
  unfold zeroTime LightMaskErase.time
  omega
end ThreeSum.LightTernaryCodes
