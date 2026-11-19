-- Prove2me | solution 1 for RHX100000.Edge.piece_30
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:51:05.065202+00:00
-- url     : https://prove2.me/submissions/20874921-fcf3-4b5d-94ff-b46fe45c045c

import Definitions.Def_RHX_Edge100000Data
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4

namespace RHX100000.Edge.P30
theorem h0 : (Nat.ble 2 30000 && Nat.ble 1 (RHX100000.Edge.E.pc 30).q && Nat.ble 1 (RHX100000.Edge.E.pc 30).rd && Nat.ble 1 (RHX100000.Edge.E.pc 30).FD) = true := by decide +kernel
theorem hc : (let c := ArbEcon.OrderK.cfg64 100000 0
    let s1 := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 30).oc (30000 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 30).oc 1 s1
    H1000Oct.checkOct c (RHX100000.Edge.E.pc 30).oc 6 30000 5 s1.acc sN.acc (RHX100000.Edge.E.pc 30).rn (RHX100000.Edge.E.pc 30).rd (RHX100000.Edge.E.pc 30).FN (RHX100000.Edge.E.pc 30).FD (RHX100000.Edge.E.pc 30).kk) = true := by decide +kernel
theorem hg : (let c := ArbEcon.OrderK.cfg64 100000 0
    let s1 := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 30).oc (30000 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (RHX100000.Edge.E.pc 30).oc 1 s1
    geomOK 100000 0 RHX100000.Edge.E.L sN.lhi (RHX100000.Edge.E.pc 30)) = true := by decide +kernel
theorem hG : gOK 30000 (RHX100000.Edge.E.pc 30) = true := by decide +kernel
theorem hr : remOK 100000 0 30000 (RHX100000.Edge.E.pc 30) = true := by decide +kernel
theorem hb : budgetOK 30000 RHX100000.Edge.E.L (RHX100000.Edge.E.pc 30) = true := by decide +kernel
theorem i1 : inRad (RHX100000.Edge.E.x 30) (RHX100000.Edge.E.pc 30) = true := by decide +kernel
theorem i2 : inRad (RHX100000.Edge.E.x (30 + 1)) (RHX100000.Edge.E.pc 30) = true := by decide +kernel
theorem ok : pieceOK 100000 0 30000 RHX100000.Edge.E.L (RHX100000.Edge.E.pc 30) = true := RHX.pieceOK_of _ _ _ _ _ h0 hc hg hG hr hb
end RHX100000.Edge.P30

theorem RHX100000.Edge.piece_30 : H11K.pieceJ RHX100000.Edge.E 30 = true :=
  RHX.pieceJ_of _ _ RHX100000.Edge.P30.ok RHX100000.Edge.P30.i1 RHX100000.Edge.P30.i2
open Arb4 in
theorem solution : H11K.pieceJ RHX100000.Edge.E 30 = true := by
  apply RHX100000.Edge.piece_30 <;> assumption
