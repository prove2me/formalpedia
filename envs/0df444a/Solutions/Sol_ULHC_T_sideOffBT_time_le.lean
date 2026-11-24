-- Prove2me | solution 1 for ULHC.T.sideOffBT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:59.264011+00:00
-- url     : https://prove2.me/submissions/958591ab-e5fb-4b82-9f2d-b89d279f6e30

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
import Theorems.Thm_ULHC_T_latOKT_ret
import Theorems.Thm_ULHC_T_stripScanT_ret
import Theorems.Thm_ULHC_T_stripLenT_ret
import Theorems.Thm_ULHC_T_allStripsT_ret
import Theorems.Thm_ULHC_T_flipT_ret
import Theorems.Thm_ULHC_T_validBT_ret
import Theorems.Thm_ULHC_T_sideOffBT_ret
import Theorems.Thm_ULHC_T_midBT_ret
import Theorems.Thm_ULHC_T_endOffBT_ret
import Theorems.Thm_ULHC_T_notEndBT_ret
import Theorems.Thm_ULHC_T_cr2BT_ret
import Theorems.Thm_ULHC_T_chainOKBT_ret
import Theorems.Thm_ULHC_T_gsrcT_ret
import Theorems.Thm_ULHC_T_gedgeT_ret
import Theorems.Thm_ULHC_T_candT_ret
import Theorems.Thm_ULHC_T_candNT_ret
import Theorems.Thm_ULHC_T_memNot_time_le
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_T_allT_time_le
import Theorems.Thm_ULHC_T_card_cellE_le
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_lallT_time_le
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v
attribute [local simp] ULHC.T.cclsT_ret
attribute [local simp] ULHC.T.cncompT_ret
attribute [local simp] ULHC.T.connBT_ret
attribute [local simp] ULHC.T.creachT_ret
attribute [local simp] ULHC.T.degT_ret
attribute [local simp] ULHC.T.fnbrT_ret
attribute [local simp] ULHC.T.isCellT_ret
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.time_tick


attribute [local simp] ULHC.T.latOKT_ret
attribute [local simp] ULHC.T.stripScanT_ret
attribute [local simp] ULHC.T.stripLenT_ret
attribute [local simp] ULHC.T.allStripsT_ret
attribute [local simp] ULHC.T.flipT_ret
attribute [local simp] ULHC.T.validBT_ret
attribute [local simp] ULHC.T.sideOffBT_ret
attribute [local simp] ULHC.T.midBT_ret
attribute [local simp] ULHC.T.endOffBT_ret
attribute [local simp] ULHC.T.notEndBT_ret
attribute [local simp] ULHC.T.cr2BT_ret
attribute [local simp] ULHC.T.chainOKBT_ret
attribute [local simp] ULHC.T.gsrcT_ret
attribute [local simp] ULHC.T.gedgeT_ret
attribute [local simp] ULHC.T.candT_ret
attribute [local simp] ULHC.T.candNT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (b c : StripSpec) : (sideOffBT b c).time ≤ sideOffBCost b c := by
  have hall : ∀ i j, (allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))).time ≤ 8 := by
    intro i j
    have := allT_time_le (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j)) 1 (fun e _ => memNot_time_le e _)
    have := card_cellE_le (cellJ c.c c.s j)
    nlinarith
  have hrow : ∀ j, (lallT (fun i => allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))) (List.range (b.n - 1))).time ≤ (b.n - 1) * 9 := by
    intro j
    have := lallT_time_le _ (List.range (b.n - 1)) 8 (fun i _ => hall i j)
    simpa using this
  have hout := lallT_time_le (fun j => lallT (fun i => allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))) (List.range (b.n - 1))) (List.range c.n)
    ((b.n - 1) * 9) (fun j _ => hrow j)
  simp only [List.length_range] at hout
  simp only [sideOffBT, time_bind, rangeT, sideOffBCost]
  have h9 : (b.n - 1) * 9 + 1 + 1 ≤ 20 * b.n + 2 := by omega
  have hm : c.n * ((b.n - 1) * 9 + 1) + c.n ≤ c.n * (20 * b.n + 2) := by
    have := Nat.mul_le_mul_left c.n h9
    rw [Nat.mul_add c.n _ 1, Nat.mul_one] at this
    exact this
  omega
end ULHC.T
