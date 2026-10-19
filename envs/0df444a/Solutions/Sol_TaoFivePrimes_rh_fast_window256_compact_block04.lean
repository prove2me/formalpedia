-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:16:14.826163+00:00
-- url     : https://prove2.me/submissions/f43c99c4-2059-42ff-8da1-57dc1b67b099

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 128 32=true := by decide +kernel
#print axioms solution
