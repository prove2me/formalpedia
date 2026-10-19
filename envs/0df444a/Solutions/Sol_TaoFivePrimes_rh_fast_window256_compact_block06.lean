-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:39:36.799907+00:00
-- url     : https://prove2.me/submissions/5fc2a4be-810e-4172-946f-d1faca40e7d6

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 192 32=true := by decide +kernel
#print axioms solution
