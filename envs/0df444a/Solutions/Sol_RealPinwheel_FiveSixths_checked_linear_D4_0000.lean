-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D4_0000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:31:26.860195+00:00
-- url     : https://prove2.me/submissions/8d50ada9-f8d0-4868-9a4f-c0621f5a5069

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD4_0000
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 69 codeFunctionD4 linearContextD4_0000 linearTreeD4_0000 = true := by
  unfold linearTreeD4_0000
  decide +kernel
