-- Prove2me | solution 1 for ULHC.T.fnbrT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:41.439943+00:00
-- url     : https://prove2.me/submissions/2ef6caa3-9447-4b0f-8861-9c558e22ae84

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_T_lfilterT_time_le
import Theorems.Thm_ULHC_T_lmapT_time_le
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
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.time_tick


attribute [local simp] ULHC.T.isCellT_ret
attribute [local simp] ULHC.T.degT_ret
attribute [local simp] ULHC.T.fnbrT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (F : Finset Edge) (u : Pt) : (fnbrT F u).time ≤ 17 := by
  have h1 := lfilterT_time_le (fun e => memT e F) (TF.inc4 u) 1 (fun _ _ => le_rfl)
  have hl : (TF.inc4 u).length = 4 := rfl
  have hlen : (TF.inc4 u |>.filter (fun e => (memT e F).ret)).length ≤ 4 :=
    (List.length_filter_le _ _).trans hl.le
  have h2 := lmapT_time_le (fun e => (pure (other e u) : TimeM Pt))
    ((TF.inc4 u).filter (fun e => (memT e F).ret)) 0 (fun _ _ => le_rfl)
  simp only [fnbrT, time_bind, toFinsetT, lmapT, List.length_map]
  simp only [lfilterT] at h1 ⊢
  simp only [lmapT] at h2
  rw [hl] at h1
  omega
end ULHC.T
