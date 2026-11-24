-- Prove2me | solution 1 for ULHC.T.stripScanT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:43.960306+00:00
-- url     : https://prove2.me/submissions/5974e7a1-aa1b-4f12-aa0d-c235867b297b

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
import Theorems.Thm_ULHC_T_latOKT_time
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
import Theorems.Thm_ULHC_T_isCellT_time
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, (stripScanT V F c s k j).time ≤ stripScanCost V F c s k j
  | 0, _ => by simp [stripScanT, stripScanCost]
  | k + 1, j => by
    have ih := solution V F c s k (j + 1)
    simp only [stripScanT, stripScanCost, time_bind, isCellT_time, latOKT_time,
      isCellT_ret, latOKT_ret, memT, time_tick]
    by_cases h1 : IsCell V (cellJ c s j) ∧ LatOK F c s j
    · rw [if_pos h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = true := by
        simp [h1.1, h1.2]
      rw [if_pos hb]
      by_cases h2 : front (cellJ c s j) s ∈ F <;> by_cases h3 : j % 2 = 0 <;> simp [h2, h3] <;> omega
    · rw [if_neg h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = false := by
        simpa using h1
      rw [hb]
      simp
end ULHC.T
