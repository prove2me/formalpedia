-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:12:43.228865+00:00
-- url     : https://prove2.me/submissions/e62860ad-c70e-4e0d-8e88-cc30b3b753f7

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution : RHFastWindow256CompactReference.block 96 32=true := by decide +kernel
#print axioms solution
