-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:10.482988+00:00
-- url     : https://prove2.me/submissions/cf16cc46-73fa-4d3a-8202-fb8a1b1a5370

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockCoefficients
theorem _root_.solution (J L : ℕ) : time J L ≤ 300*(J+1)*(L+1) := by
  unfold time roundTime LightScaleArray.time powTableTime
  nlinarith
end ThreeSum.LightBlockCoefficients
