-- Prove2me | solution 1 for ULHC.card_nbr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:06.136266+00:00
-- url     : https://prove2.me/submissions/204032b6-8bd8-4dc9-963a-c7c21460f5f7

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
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
open Finset TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (u : Pt) : (nbr V F u).card ≤ 4 := by
  unfold nbr
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [inc4])
end ULHC
