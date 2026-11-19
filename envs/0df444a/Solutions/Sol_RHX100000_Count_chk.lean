-- Prove2me | solution 1 for RHX100000.Count.chk
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:45:08.131481+00:00
-- url     : https://prove2.me/submissions/726f8478-08f0-4d46-99d8-c95abe30d756

import Definitions.Def_RHX_Count100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem RHX100000.Count.chk :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 100000) (Q.frac 100121 2)
      (Q.frac 9975814658 4) 138031 RHX100000.Count.E &&
      k6sideB RHX100000.Count.G0 RHX100000.Count.G1 RHX100000.Count.E) = true := by
  decide +kernel
open Arb4 Arb4.Q in
theorem solution :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 100000) (Q.frac 100121 2)
      (Q.frac 9975814658 4) 138031 RHX100000.Count.E &&
      k6sideB RHX100000.Count.G0 RHX100000.Count.G1 RHX100000.Count.E) = true := by
  apply RHX100000.Count.chk <;> assumption
