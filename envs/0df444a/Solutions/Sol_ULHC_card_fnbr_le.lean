-- Prove2me | solution 1 for ULHC.card_fnbr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:16.486309+00:00
-- url     : https://prove2.me/submissions/b65e9418-adf6-44ec-8ef2-3346ff946b53

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (F : Finset Edge) (u : Pt) : (fnbr F u).card ≤ 4 := by
  unfold fnbr
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [TF.inc4])
end ULHC
