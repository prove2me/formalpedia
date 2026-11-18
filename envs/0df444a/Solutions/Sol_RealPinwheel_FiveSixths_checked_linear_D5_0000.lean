-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D5_0000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:23:49.436118+00:00
-- url     : https://prove2.me/submissions/0faeb747-f59e-43e5-81e4-83251939a300

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0000
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 216 codeFunctionD5 linearContextD5_0000 linearTreeD5_0000 = true := by
  unfold linearTreeD5_0000
  decide +kernel
