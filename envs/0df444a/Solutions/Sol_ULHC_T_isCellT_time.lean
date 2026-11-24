-- Prove2me | solution 1 for ULHC.T.isCellT_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:31.818945+00:00
-- url     : https://prove2.me/submissions/410f546f-cefb-42ea-943b-e0077e070be0

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
import Theorems.Thm_ULHC_T_isCellT_ret
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

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (c : Pt) : (isCellT V c).time = 7 := by
  simp [isCellT, memT]
end ULHC.T
