-- Prove2me | solution 1 for RHX100000.Edge.piece_35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:51:15.308225+00:00
-- url     : https://prove2.me/submissions/279070ca-16eb-4da5-a784-e7e9b6d9bc72

import Definitions.Def_RHX_Edge100000Data
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4

namespace RHX100000.Edge.P35
theorem h0 : (Nat.ble 2 30000 && Nat.ble 1 (RHX100000.Edge.E.pc 35).q && Nat.ble 1 (RHX100000.Edge.E.pc 35).rd && Nat.ble 1 (RHX100000.Edge.E.pc 35).FD) = true := by decide +kernel
theorem hc : (let c := ArbEcon.OrderK.cfg64 100000 0
    let s1 := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 35).oc (30000 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 35).oc 1 s1
    H1000Oct.checkOct c (RHX100000.Edge.E.pc 35).oc 6 30000 5 s1.acc sN.acc (RHX100000.Edge.E.pc 35).rn (RHX100000.Edge.E.pc 35).rd (RHX100000.Edge.E.pc 35).FN (RHX100000.Edge.E.pc 35).FD (RHX100000.Edge.E.pc 35).kk) = true := by decide +kernel
theorem hg : (let c := ArbEcon.OrderK.cfg64 100000 0
    let s1 := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 35).oc (30000 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 35).oc 1 s1
    geomOK 100000 0 RHX100000.Edge.E.L sN.lhi (RHX100000.Edge.E.pc 35)) = true := by decide +kernel
theorem hG : gOK 30000 (RHX100000.Edge.E.pc 35) = true := by decide +kernel
theorem hr : remOK 100000 0 30000 (RHX100000.Edge.E.pc 35) = true := by decide +kernel
theorem hb : budgetOK 30000 RHX100000.Edge.E.L (RHX100000.Edge.E.pc 35) = true := by decide +kernel
theorem i1 : inRad (RHX100000.Edge.E.x 35) (RHX100000.Edge.E.pc 35) = true := by decide +kernel
theorem i2 : inRad (RHX100000.Edge.E.x (35 + 1)) (RHX100000.Edge.E.pc 35) = true := by decide +kernel
theorem ok : pieceOK 100000 0 30000 RHX100000.Edge.E.L (RHX100000.Edge.E.pc 35) = true := RHX.pieceOK_of _ _ _ _ _ h0 hc hg hG hr hb
end RHX100000.Edge.P35

theorem RHX100000.Edge.piece_35 : H11K.pieceJ RHX100000.Edge.E 35 = true :=
  RHX.pieceJ_of _ _ RHX100000.Edge.P35.ok RHX100000.Edge.P35.i1 RHX100000.Edge.P35.i2
open Arb4 in
theorem solution : H11K.pieceJ RHX100000.Edge.E 35 = true := by
  apply RHX100000.Edge.piece_35 <;> assumption
