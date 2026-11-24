-- Prove2me | solution 1 for ULHC.T.creachT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:30:01.612831+00:00
-- url     : https://prove2.me/submissions/4c51de89-3e0c-4381-8c49-4d5d6b52ca09

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_fnbrT_time_le
import Theorems.Thm_ULHC_T_creachT_ret
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

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (F : Finset Edge) (x : Pt) : ∀ k, (creachT F x k).time ≤ creachCost F x k
  | 0 => by simp [creachT, creachCost]
  | k + 1 => by
    have ih := solution F x k
    simp only [creachT, time_bind, creachT_ret, biUnionT, unionT, fnbrT_ret, creachCost]
    have hs : ∑ u ∈ creach F x k, ((fnbrT F u).time + (fnbr F u).card + 1) ≤
        ∑ u ∈ creach F x k, (fnbrCost + (fnbr F u).card) :=
      Finset.sum_le_sum (fun u _ => by have := fnbrT_time_le F u; unfold fnbrCost; omega)
    have he : ((creach F x k).biUnion fun u => fnbr F u).card =
        ((creach F x k).biUnion (fnbr F)).card := rfl
    omega
end ULHC.T
