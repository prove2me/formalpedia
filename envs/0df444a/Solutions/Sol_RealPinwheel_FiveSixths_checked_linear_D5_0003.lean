-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D5_0003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:24:51.95097+00:00
-- url     : https://prove2.me/submissions/1c47a680-c468-4ac9-96a7-0190ad867545

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0003
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 216 codeFunctionD5 linearContextD5_0003 linearTreeD5_0003 = true := by
  unfold linearTreeD5_0003
  decide +kernel
