-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:02:05.935987+00:00
-- url     : https://prove2.me/submissions/4531d85c-1a9f-4690-8915-66312f43eeb2

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 32 32=true := by decide +kernel
#print axioms solution
