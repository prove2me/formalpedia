-- Prove2me | solution 1 for RHX1000000.Edge.rest
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:21:03.87317+00:00
-- url     : https://prove2.me/submissions/b377d8e5-741b-42f0-93f8-4a6b160cb0b0

import Theorems.Thm_RHX1000000_Run_E00_blk0
import Theorems.Thm_RHX1000000_Run_E00_blk1
import Theorems.Thm_RHX1000000_Run_E00_blk2
import Theorems.Thm_RHX1000000_Run_E00_blk3
import Theorems.Thm_RHX1000000_Run_E00_blk4
import Theorems.Thm_RHX1000000_Run_E00_blk5
import Theorems.Thm_RHX1000000_Run_E00_blk6
import Theorems.Thm_RHX1000000_Run_E00_blk7
import Theorems.Thm_RHX1000000_Run_E00_blk8
import Theorems.Thm_RHX1000000_Run_E00_blk9
import Theorems.Thm_RHX1000000_Run_E00_run
import Theorems.Thm_RHX1000000_Run_E72_blk0
import Theorems.Thm_RHX1000000_Run_E72_blk1
import Theorems.Thm_RHX1000000_Run_E72_blk2
import Theorems.Thm_RHX1000000_Run_E72_blk3
import Theorems.Thm_RHX1000000_Run_E72_blk4
import Theorems.Thm_RHX1000000_Run_E72_blk5
import Theorems.Thm_RHX1000000_Run_E72_blk6
import Theorems.Thm_RHX1000000_Run_E72_blk7
import Theorems.Thm_RHX1000000_Run_E72_blk8
import Theorems.Thm_RHX1000000_Run_E72_blk9
import Theorems.Thm_RHX1000000_Run_E72_run
import Theorems.Thm_RHX_accBeq_eq
import Theorems.Thm_RHX_accsBeq_eq
import Theorems.Thm_RHX_boxOK_of_run
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_cellOK_of_run
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
import Theorems.Thm_RHX_pieceOK_of_run
import Theorems.Thm_RHX_runO_add
import Theorems.Thm_RHX_runO_chain
import Theorems.Thm_RHX_runO_succ
import Theorems.Thm_RHX_slabOK_of
import Theorems.Thm_RHX_stoBeq_eq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

namespace RHX1000000.Edge.Rest
theorem hh : (Nat.ble 1 RHX1000000.Edge.E.m && Nat.ble 1 RHX1000000.Edge.E.tn && eqB (RHX1000000.Edge.E.x 0) (ofNat 2) && eqB (RHX1000000.Edge.E.x RHX1000000.Edge.E.m) (ofInt (-1)) &&
    (List.range (RHX1000000.Edge.E.m - 1)).all (fun j => decide (|(RHX1000000.Edge.E.pc (j + 1)).kk - (RHX1000000.Edge.E.pc j).kk| ≤ 3)) &&
    eqB (RHX1000000.Edge.E.pc 0).σQ (ofNat 2) && eqB (RHX1000000.Edge.E.pc (RHX1000000.Edge.E.m - 1)).σQ (ofInt (-1))) = true := by decide +kernel
theorem hb0 : boxOK 1000000 0 300000 (RHX1000000.Edge.E.pc 0) RHX1000000.Edge.E.D0 RHX1000000.Edge.E.reLo0 RHX1000000.Edge.E.reHi0 RHX1000000.Edge.E.imLo0 RHX1000000.Edge.E.imHi0 RHX1000000.Edge.E.Qp0 RHX1000000.Edge.E.Rn0 RHX1000000.Edge.E.Rd0
    RHX1000000.Edge.E.qlo0 RHX1000000.Edge.E.qhi0 = true :=
  RHX.boxOK_of_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RHX1000000.Run.E00.run (by decide +kernel)
theorem hb1 : boxOK 1000000 0 300000 (RHX1000000.Edge.E.pc 72) RHX1000000.Edge.E.D1 RHX1000000.Edge.E.reLo1 RHX1000000.Edge.E.reHi1 RHX1000000.Edge.E.imLo1 RHX1000000.Edge.E.imHi1 RHX1000000.Edge.E.Qp1 RHX1000000.Edge.E.Rn1 RHX1000000.Edge.E.Rd1
    RHX1000000.Edge.E.qlo1 RHX1000000.Edge.E.qhi1 = true :=
  RHX.boxOK_of_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RHX1000000.Run.E72.run (by decide +kernel)
theorem hlo : finalLoOK ((RHX1000000.Edge.E.pc (RHX1000000.Edge.E.m - 1)).kk - (RHX1000000.Edge.E.pc 0).kk) RHX1000000.Edge.E.qhi0 RHX1000000.Edge.E.qlo1 RHX1000000.Edge.E.Lo = true := by decide +kernel
theorem hhi : finalHiOK ((RHX1000000.Edge.E.pc (RHX1000000.Edge.E.m - 1)).kk - (RHX1000000.Edge.E.pc 0).kk) RHX1000000.Edge.E.qlo0 RHX1000000.Edge.E.qhi1 RHX1000000.Edge.E.Hi = true := by decide +kernel
end RHX1000000.Edge.Rest

theorem RHX1000000.Edge.rest : H11K.edgeRest RHX1000000.Edge.E = true :=
  RHX.edgeRest_of _ RHX1000000.Edge.Rest.hh RHX1000000.Edge.Rest.hb0 RHX1000000.Edge.Rest.hb1 RHX1000000.Edge.Rest.hlo RHX1000000.Edge.Rest.hhi
open Arb4 Arb4.Q in
theorem solution : H11K.edgeRest RHX1000000.Edge.E = true := by
  apply RHX1000000.Edge.rest <;> assumption
