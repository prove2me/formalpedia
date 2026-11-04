-- Prove2me | solution 1 for ThreeSum.LightTernaryCodes.digit_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:55.39317+00:00
-- url     : https://prove2.me/submissions/062c8ee6-bdc1-4a74-bef9-d1910e736576

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryCodes
theorem _root_.solution (W : ℕ) : digitTime W ≤ 400*(W+1) := by
  unfold digitTime LightMaskErase.time
  omega
end ThreeSum.LightTernaryCodes
