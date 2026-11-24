-- Prove2me | solution 1 for ULHC.T.nextT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:50.135226+00:00
-- url     : https://prove2.me/submissions/f18d06ad-61bb-4983-8be9-07b5ea5475d5

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
import Theorems.Thm_ULHC_T_lookT_ret
import Theorems.Thm_ULHC_T_aminT_ret
import Theorems.Thm_ULHC_T_stepT_ret
import Theorems.Thm_ULHC_T_nextT_ret
import Theorems.Thm_ULHC_T_layerT_ret
import Theorems.Thm_ULHC_T_pickSrcT_ret
import Theorems.Thm_ULHC_T_minPathLT_ret
import Theorems.Thm_ULHC_T_minPathT_ret
import Theorems.Thm_ULHC_T_lsum_mono
import Theorems.Thm_ULHC_T_stepT_time_le
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


attribute [local simp] ULHC.T.lookT_ret
attribute [local simp] ULHC.T.aminT_ret
attribute [local simp] ULHC.T.stepT_ret
attribute [local simp] ULHC.T.nextT_ret
attribute [local simp] ULHC.T.layerT_ret
attribute [local simp] ULHC.T.pickSrcT_ret
attribute [local simp] ULHC.T.minPathLT_ret
attribute [local simp] ULHC.T.minPathT_ret

set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
namespace ULHC.T
theorem _root_.solution (tbl : List (α × Option (ℕ × List α))) :
    (nextT NL mid tgt edgeT w tbl).time ≤ MP.nextCost NL mid tgt (fun a b => (edgeT a b).time) tbl := by
  simp only [nextT, lmapT, MP.nextCost, time_bind, time_pure]
  exact lsum_mono NL _ _ (fun x _ => by have := stepT_time_le NL mid tgt edgeT w tbl x; omega)
end ULHC.T
