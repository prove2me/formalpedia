-- Prove2me | solution 1 for OddGoldbach19.packed_numeric8000
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:23:59.364241+00:00
-- url     : https://prove2.me/submissions/980546bd-7a31-45b1-871c-a8ff635e8c14

import Definitions.Def_OddGoldbach19_PackedData8000
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
open OddGoldbach19.Packed8000
theorem solution :
    ((packedQ*packedR*packedW)/(2^64)^(2*40907))%(2^64)=557349373474 := by
  decide +kernel
#print axioms solution
