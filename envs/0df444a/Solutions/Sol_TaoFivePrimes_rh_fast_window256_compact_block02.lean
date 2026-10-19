-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:58:59.222588+00:00
-- url     : https://prove2.me/submissions/2c578090-e1e4-4b77-a215-f1a218df64af

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 64 32=true := by decide +kernel
#print axioms solution
