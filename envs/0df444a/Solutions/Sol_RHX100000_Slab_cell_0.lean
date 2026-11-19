-- Prove2me | solution 1 for RHX100000.Slab.cell_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:55:30.945533+00:00
-- url     : https://prove2.me/submissions/f77fdfce-6b7a-4a27-af6b-5ab9070ffbab

import Definitions.Def_RHX_Slab100000Data
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

namespace RHX100000.Slab.C0
theorem h0 : (Nat.ble 2 30001 && Nat.ble 1 (RHX100000.Slab.S.cell 0).q && Nat.ble 1 (RHX100000.Slab.S.cell 0).rd && Nat.ble (RHX100000.Slab.S.cell 0).b (RHX100000.Slab.S.cell 0).a) = true := by decide +kernel
theorem hc : (let c := ArbEcon.OrderK.cfg64 1638400025 14
    let s1 := ArbEcon.Off.runO c (⟨49, 0, 96, 2 ^ 6144, 256⟩ : ArbEcon.Off.OCfg) (30001 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (⟨49, 0, 96, 2 ^ 6144, 256⟩ : ArbEcon.Off.OCfg) 1 s1
    ArbEcon.Off.checkCell c (⟨49, 0, 96, 2 ^ 6144, 256⟩ : ArbEcon.Off.OCfg) 6 30001 5 s1.acc sN.acc 106 10000 314126 1000000) = true := by decide +kernel
theorem hR : le (frac ((RHX100000.Slab.S.cell 0).rn : ℤ) (RHX100000.Slab.S.cell 0).rd) RHX100000.Slab.S.R = true := by decide +kernel
theorem hl : (let c := ArbEcon.OrderK.cfg64 1638400025 14
    let s1 := ArbEcon.Off.runO c (⟨49, 0, 96, 2 ^ 6144, 256⟩ : ArbEcon.Off.OCfg) (30001 - 2) (ArbEcon.Off.StO.init c 5)
    let sN := ArbEcon.Off.runO c (⟨49, 0, 96, 2 ^ 6144, 256⟩ : ArbEcon.Off.OCfg) 1 s1
    le (ofNat sN.lhi) (mul RHX100000.Slab.S.L (ofNat (2 ^ 64)))) = true := by decide +kernel
theorem r1 : le RHX100000.Slab.S.lo (tQ (RHX100000.Slab.S.cell 0).tn RHX100000.Slab.S.tq) = true := by decide +kernel
theorem r2 : le (add (npow (add (RHX100000.Slab.S.cell 0).σQ (ofNat 11)) 2) (npow (tQ (RHX100000.Slab.S.cell 0).tn RHX100000.Slab.S.tq) 2)) (npow RHX100000.Slab.S.U 2) = true := by decide +kernel
theorem r3 : le (qabs (sub (RHX100000.Slab.S.xs 0) (RHX100000.Slab.S.cell 0).σQ)) (RHX100000.Slab.S.cell 0).w = true := by decide +kernel
theorem r4 : le (qabs (sub (RHX100000.Slab.S.xs (0 + 1)) (RHX100000.Slab.S.cell 0).σQ)) (RHX100000.Slab.S.cell 0).w = true := by decide +kernel
theorem r5 : le (qabs (sub RHX100000.Slab.S.lo (tQ (RHX100000.Slab.S.cell 0).tn RHX100000.Slab.S.tq))) (RHX100000.Slab.S.cell 0).hh = true := by decide +kernel
theorem r6 : le (qabs (sub RHX100000.Slab.S.hi (tQ (RHX100000.Slab.S.cell 0).tn RHX100000.Slab.S.tq))) (RHX100000.Slab.S.cell 0).hh = true := by decide +kernel
theorem r7 : le (add (npow (RHX100000.Slab.S.cell 0).w 2) (npow (RHX100000.Slab.S.cell 0).hh 2)) (npow (frac ((RHX100000.Slab.S.cell 0).rn : ℤ) (RHX100000.Slab.S.cell 0).rd) 2) = true := by decide +kernel
end RHX100000.Slab.C0

theorem RHX100000.Slab.cell_0 : cellOK RHX100000.Slab.S 0 = true :=
  RHX.cellOK_of _ _ RHX100000.Slab.C0.h0 RHX100000.Slab.C0.hc RHX100000.Slab.C0.hR RHX100000.Slab.C0.hl
    RHX100000.Slab.C0.r1 RHX100000.Slab.C0.r2 RHX100000.Slab.C0.r3 RHX100000.Slab.C0.r4
    RHX100000.Slab.C0.r5 RHX100000.Slab.C0.r6 RHX100000.Slab.C0.r7
open Arb4 Arb4.Q in
theorem solution : cellOK RHX100000.Slab.S 0 = true := by
  apply RHX100000.Slab.cell_0 <;> assumption
