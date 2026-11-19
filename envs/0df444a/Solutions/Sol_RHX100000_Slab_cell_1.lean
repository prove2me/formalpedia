-- Prove2me | solution 1 for RHX100000.Slab.cell_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:55:32.912425+00:00
-- url     : https://prove2.me/submissions/2f8b34b2-ebc4-4552-b40a-2dc5e0c41e88

import Definitions.Def_RHX_Slab100000Data
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

namespace RHX100000.Slab.C1
theorem h0 : (Nat.ble 2 30001 && Nat.ble 1 (RHX100000.Slab.S.cell 1).q && Nat.ble 1 (RHX100000.Slab.S.cell 1).rd && Nat.ble (RHX100000.Slab.S.cell 1).b (RHX100000.Slab.S.cell 1).a) = true := by decide +kernel
theorem hc : (let c := ArbEcon.OrderK.cfg64 1638400025 14
    let s1 := ArbEcon.Off.runO c (⟨34, 0, 64, 2 ^ 4096, 256⟩ : ArbEcon.Off.OCfg) (30001 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (⟨34, 0, 64, 2 ^ 4096, 256⟩ : ArbEcon.Off.OCfg) 1 s1
    ArbEcon.Off.checkCell c (⟨34, 0, 64, 2 ^ 4096, 256⟩ : ArbEcon.Off.OCfg) 6 30001 5 s1.acc sN.acc 106 10000 314126 1000000) = true := by decide +kernel
theorem hR : le (frac ((RHX100000.Slab.S.cell 1).rn : ℤ) (RHX100000.Slab.S.cell 1).rd) RHX100000.Slab.S.R = true := by decide +kernel
theorem hl : (let c := ArbEcon.OrderK.cfg64 1638400025 14
    let s1 := ArbEcon.Off.runO c (⟨34, 0, 64, 2 ^ 4096, 256⟩ : ArbEcon.Off.OCfg) (30001 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (⟨34, 0, 64, 2 ^ 4096, 256⟩ : ArbEcon.Off.OCfg) 1 s1
    le (ofNat sN.lhi) (mul RHX100000.Slab.S.L (ofNat (2 ^ 64)))) = true := by decide +kernel
theorem r1 : le RHX100000.Slab.S.lo (tQ (RHX100000.Slab.S.cell 1).tn RHX100000.Slab.S.tq) = true := by decide +kernel
theorem r2 : le (add (npow (add (RHX100000.Slab.S.cell 1).σQ (ofNat 11)) 2) (npow (tQ (RHX100000.Slab.S.cell 1).tn RHX100000.Slab.S.tq) 2)) (npow RHX100000.Slab.S.U 2) = true := by decide +kernel
theorem r3 : le (qabs (sub (RHX100000.Slab.S.xs 1) (RHX100000.Slab.S.cell 1).σQ)) (RHX100000.Slab.S.cell 1).w = true := by decide +kernel
theorem r4 : le (qabs (sub (RHX100000.Slab.S.xs (1 + 1)) (RHX100000.Slab.S.cell 1).σQ)) (RHX100000.Slab.S.cell 1).w = true := by decide +kernel
theorem r5 : le (qabs (sub RHX100000.Slab.S.lo (tQ (RHX100000.Slab.S.cell 1).tn RHX100000.Slab.S.tq))) (RHX100000.Slab.S.cell 1).hh = true := by decide +kernel
theorem r6 : le (qabs (sub RHX100000.Slab.S.hi (tQ (RHX100000.Slab.S.cell 1).tn RHX100000.Slab.S.tq))) (RHX100000.Slab.S.cell 1).hh = true := by decide +kernel
theorem r7 : le (add (npow (RHX100000.Slab.S.cell 1).w 2) (npow (RHX100000.Slab.S.cell 1).hh 2)) (npow (frac ((RHX100000.Slab.S.cell 1).rn : ℤ) (RHX100000.Slab.S.cell 1).rd) 2) = true := by decide +kernel
end RHX100000.Slab.C1

theorem RHX100000.Slab.cell_1 : cellOK RHX100000.Slab.S 1 = true :=
  RHX.cellOK_of _ _ RHX100000.Slab.C1.h0 RHX100000.Slab.C1.hc RHX100000.Slab.C1.hR RHX100000.Slab.C1.hl
    RHX100000.Slab.C1.r1 RHX100000.Slab.C1.r2 RHX100000.Slab.C1.r3 RHX100000.Slab.C1.r4
    RHX100000.Slab.C1.r5 RHX100000.Slab.C1.r6 RHX100000.Slab.C1.r7
open Arb4 Arb4.Q in
theorem solution : cellOK RHX100000.Slab.S 1 = true := by
  apply RHX100000.Slab.cell_1 <;> assumption
