-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D5_0002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:24:14.839083+00:00
-- url     : https://prove2.me/submissions/022f33fe-7614-42d7-bbd8-273161af6e5d

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0002
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 216 codeFunctionD5 linearContextD5_0002 linearTreeD5_0002 = true := by
  unfold linearTreeD5_0002
  decide +kernel
