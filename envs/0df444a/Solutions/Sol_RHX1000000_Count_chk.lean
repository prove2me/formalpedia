-- Prove2me | solution 1 for RHX1000000.Count.chk
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:53:23.562481+00:00
-- url     : https://prove2.me/submissions/1329aca2-9fe2-40bc-b1ab-d7a45fd5e776

import Definitions.Def_RHX_Count1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem RHX1000000.Count.chk :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 1000000) (Q.frac 1000121 2)
      (Q.frac 999758014658 4) 1747108 RHX1000000.Count.E &&
      k6sideB RHX1000000.Count.G0 RHX1000000.Count.G1 RHX1000000.Count.E) = true := by
  decide +kernel
open Arb4 Arb4.Q in
theorem solution :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 1000000) (Q.frac 1000121 2)
      (Q.frac 999758014658 4) 1747108 RHX1000000.Count.E &&
      k6sideB RHX1000000.Count.G0 RHX1000000.Count.G1 RHX1000000.Count.E) = true := by
  apply RHX1000000.Count.chk <;> assumption
