-- Prove2me | solution 1 for ULHC.findT3Cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:43.308399+00:00
-- url     : https://prove2.me/submissions/dad3ef02-e3fc-43ba-8b7f-5570f0ad9d52

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_length_cellList
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_T_lsum_le
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
import Theorems.Thm_ULHC_connBCost_le
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



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) : findT3Cost V G ≤ 200 * (V.card + 1) ^ 3 := by
  have hl := length_cellList V
  have hps : ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).length =
      4 * (cellList V).length := by
    rw [List.length_flatMap]
    simp only [List.length_map]
    have : ∀ l : List Pt, (l.map fun _ => sidesL.length).sum = 4 * l.length := by
      intro l; simp [sidesL]; ring
    exact this _
  have h1 := T.lsum_le ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf))
    (fun p => t3BCost V G p.1 p.2 + 1) (11 + 30 * (V.card + 1) ^ 2) (fun p _ => by
      have := connBCost_le hGV (back1 p.1 p.2); unfold t3BCost; omega)
  rw [hps] at h1
  unfold findT3Cost cellListCost
  nlinarith
end ULHC
