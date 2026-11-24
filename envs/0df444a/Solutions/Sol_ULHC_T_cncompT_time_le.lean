-- Prove2me | solution 1 for ULHC.T.cncompT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:11.356843+00:00
-- url     : https://prove2.me/submissions/53529016-10a7-4ed7-8f77-f7d4e4e56610

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_cclsT_time_le
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
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
attribute [local simp] ULHC.T.creachT_ret
attribute [local simp] ULHC.T.cclsT_ret
attribute [local simp] ULHC.T.connBT_ret
attribute [local simp] ULHC.T.cncompT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) : (cncompT V F).time ≤ cncompCost V F := by
  simp only [cncompT, time_bind, imageSetsT, cardT, cclsT_ret, cncompCost]
  have hs : ∑ x ∈ V, ((cclsT V F x).time + (ccls V F x).card) ≤
      ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) :=
    Finset.sum_le_sum (fun x _ => by have := cclsT_time_le V F x; omega)
  have hc : (V.image (fun x => ccls V F x)).card ≤ V.card := card_image_le
  omega
end ULHC.T
