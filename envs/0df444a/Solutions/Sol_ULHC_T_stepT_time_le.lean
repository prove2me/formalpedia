-- Prove2me | solution 1 for ULHC.T.stepT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:18.782971+00:00
-- url     : https://prove2.me/submissions/42d43685-fc2f-4231-862c-9e3d68304b8d

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
import Theorems.Thm_ULHC_T_lookT_time_le
import Theorems.Thm_ULHC_T_aminT_time
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
theorem _root_.solution (tbl : List (α × Option (ℕ × List α))) (x : α) :
    (stepT NL mid tgt edgeT w tbl x).time ≤
      MP.stepCost NL mid tgt (fun a b => (edgeT a b).time) tbl x := by
  unfold stepT MP.stepCost
  by_cases h1 : tgt x = true
  · simp [h1]
  · by_cases h2 : mid x = true
    · simp only [h1, h2, time_bind, time_tick, time_pure, Bool.false_eq_true, ite_false, ite_true,
        aminT_time]
      have := lsum_mono NL (fun y => (do
          let e ← edgeT x y
          let tf ← lookT y tbl
          tick 3
          pure (if e then extend x (w x) tf else none) : TimeM (Option (ℕ × List α))).time + 1)
        (fun y => (edgeT x y).time + MP.lookCost tbl + 4) (fun y _ => by
          have := lookT_time_le y tbl
          simp only [time_bind, time_tick, time_pure, MP.lookCost]
          omega)
      simp only [time_bind, time_tick, time_pure] at this
      omega
    · simp [h1, h2]
end ULHC.T
