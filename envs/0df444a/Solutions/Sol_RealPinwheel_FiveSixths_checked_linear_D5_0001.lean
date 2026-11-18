-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D5_0001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:14.512774+00:00
-- url     : https://prove2.me/submissions/8f4bf2d8-e677-4074-93d9-7ac41611bfbc

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0001
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 216 codeFunctionD5 linearContextD5_0001 linearTreeD5_0001 = true := by
  unfold linearTreeD5_0001
  decide +kernel
