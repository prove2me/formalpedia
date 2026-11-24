-- Prove2me | solution 1 for ULHC.T.card_cellE_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:41.403841+00:00
-- url     : https://prove2.me/submissions/ece0eb3b-a160-4e61-8f39-111852ec4fa2

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.time_bind

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (c : Pt) : (cellE c).card ≤ 4 := by
  unfold cellE
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))
end ULHC.T
