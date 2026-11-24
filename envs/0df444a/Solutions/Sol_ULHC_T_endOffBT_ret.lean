-- Prove2me | solution 1 for ULHC.T.endOffBT_ret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:14.554595+00:00
-- url     : https://prove2.me/submissions/d908bc2e-58b7-4a3b-acf9-82386ad545b5

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
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_isCellT_ret
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

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (b c : StripSpec) : (endOffBT b c).ret = endOffB b c := by
  unfold endOffBT endOffB
  by_cases h : c.n % 2 = 0 <;> simp [allT, memT, h]
end ULHC.T
