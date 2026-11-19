-- Prove2me | solution 1 for RHX100000.Edge.rest
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:55:29.094216+00:00
-- url     : https://prove2.me/submissions/01cda316-6d8d-466f-acda-64435eefd067

import Definitions.Def_RHX_Edge100000Data
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

namespace RHX100000.Edge.Rest
theorem hh : (Nat.ble 1 RHX100000.Edge.E.m && Nat.ble 1 RHX100000.Edge.E.tn && eqB (RHX100000.Edge.E.x 0) (ofNat 2) && eqB (RHX100000.Edge.E.x RHX100000.Edge.E.m) (ofInt (-1)) &&
    (List.range (RHX100000.Edge.E.m - 1)).all (fun j => decide (|(RHX100000.Edge.E.pc (j + 1)).kk - (RHX100000.Edge.E.pc j).kk| ≤ 3)) &&
    eqB (RHX100000.Edge.E.pc 0).σQ (ofNat 2) && eqB (RHX100000.Edge.E.pc (RHX100000.Edge.E.m - 1)).σQ (ofInt (-1))) = true := by decide +kernel
theorem hb0 : boxOK 100000 0 30000 (RHX100000.Edge.E.pc 0) RHX100000.Edge.E.D0 RHX100000.Edge.E.reLo0 RHX100000.Edge.E.reHi0 RHX100000.Edge.E.imLo0 RHX100000.Edge.E.imHi0 RHX100000.Edge.E.Qp0 RHX100000.Edge.E.Rn0 RHX100000.Edge.E.Rd0
    RHX100000.Edge.E.qlo0 RHX100000.Edge.E.qhi0 = true := by decide +kernel
theorem hb1 : boxOK 100000 0 30000 (RHX100000.Edge.E.pc 40) RHX100000.Edge.E.D1 RHX100000.Edge.E.reLo1 RHX100000.Edge.E.reHi1 RHX100000.Edge.E.imLo1 RHX100000.Edge.E.imHi1 RHX100000.Edge.E.Qp1 RHX100000.Edge.E.Rn1 RHX100000.Edge.E.Rd1
    RHX100000.Edge.E.qlo1 RHX100000.Edge.E.qhi1 = true := by decide +kernel
theorem hlo : finalLoOK ((RHX100000.Edge.E.pc (RHX100000.Edge.E.m - 1)).kk - (RHX100000.Edge.E.pc 0).kk) RHX100000.Edge.E.qhi0 RHX100000.Edge.E.qlo1 RHX100000.Edge.E.Lo = true := by decide +kernel
theorem hhi : finalHiOK ((RHX100000.Edge.E.pc (RHX100000.Edge.E.m - 1)).kk - (RHX100000.Edge.E.pc 0).kk) RHX100000.Edge.E.qlo0 RHX100000.Edge.E.qhi1 RHX100000.Edge.E.Hi = true := by decide +kernel
end RHX100000.Edge.Rest

theorem RHX100000.Edge.rest : H11K.edgeRest RHX100000.Edge.E = true :=
  RHX.edgeRest_of _ RHX100000.Edge.Rest.hh RHX100000.Edge.Rest.hb0 RHX100000.Edge.Rest.hb1
    RHX100000.Edge.Rest.hlo RHX100000.Edge.Rest.hhi
open Arb4 Arb4.Q in
theorem solution : H11K.edgeRest RHX100000.Edge.E = true := by
  apply RHX100000.Edge.rest <;> assumption
