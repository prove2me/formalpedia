-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_block00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:48:31.169025+00:00
-- url     : https://prove2.me/submissions/1a0a4f50-1d4c-47ac-989a-7b0ea86625a1

import Definitions.Def_TaoFivePrimes_RHFastWindow256Reference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256Reference.block 0 32=true := by decide +kernel
#print axioms solution
