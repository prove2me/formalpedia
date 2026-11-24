-- Prove2me | solution 1 for ULHC.T.layerT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:50.918815+00:00
-- url     : https://prove2.me/submissions/67f4bb15-3d2c-4d89-8136-8131b352daf0

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
import Theorems.Thm_ULHC_T_nextT_time_le
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution : ∀ k, (layerT NL mid tgt edgeT w k).time ≤
    MP.layerCost NL mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time) k
  | 0 => by simp [layerT, MP.layerCost]
  | k + 1 => by
    have ih := solution k
    have := nextT_time_le NL mid tgt edgeT w (layerT NL mid tgt edgeT w k).ret
    simp only [layerT_ret] at this
    simp only [layerT, MP.layerCost, time_bind, layerT_ret]
    omega
end ULHC.T
