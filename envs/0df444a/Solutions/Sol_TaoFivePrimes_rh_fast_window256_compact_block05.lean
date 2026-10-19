-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:26:05.988667+00:00
-- url     : https://prove2.me/submissions/31586016-2495-48b6-921c-4e6745af95c2

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 160 32=true := by decide +kernel
#print axioms solution
