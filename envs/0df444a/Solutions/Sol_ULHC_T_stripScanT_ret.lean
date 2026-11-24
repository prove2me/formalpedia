-- Prove2me | solution 1 for ULHC.T.stripScanT_ret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:49.822027+00:00
-- url     : https://prove2.me/submissions/7ad92f34-9689-427a-b84f-ebc55b1da6a9

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
import Theorems.Thm_ULHC_T_latOKT_ret
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

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, (stripScanT V F c s k j).ret = stripScan V F c s k j
  | 0, _ => rfl
  | k + 1, j => by
    have ih := solution V F c s k (j + 1)
    simp only [stripScanT, stripScan, ret_bind, isCellT_ret, latOKT_ret, memT]
    by_cases h1 : IsCell V (cellJ c s j) ∧ LatOK F c s j
    · rw [if_pos h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = true := by
        simp [h1.1, h1.2]
      rw [if_pos hb]
      by_cases h2 : front (cellJ c s j) s ∈ F <;> by_cases h3 : j % 2 = 0 <;>
        simp [h2, h3, ih]
    · rw [if_neg h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = false := by
        simpa using h1
      rw [hb]
      rfl
end ULHC.T
