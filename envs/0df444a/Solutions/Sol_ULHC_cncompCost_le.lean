-- Prove2me | solution 1 for ULHC.cncompCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:56.443551+00:00
-- url     : https://prove2.me/submissions/72ad1381-e74f-47bb-9bb8-1dcb726edbb6

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_card_creach_le
import Theorems.Thm_ULHC_connBCost_le
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) :
    cncompCost V F ≤ 32 * (V.card + 1) ^ 3 := by
  unfold cncompCost
  have h : ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) ≤
      V.card * (30 * (V.card + 1) ^ 2 + (V.card + 1)) := by
    have := Finset.sum_le_card_nsmul V (fun x => cclsCost V F x + (ccls V F x).card + 1)
      (30 * (V.card + 1) ^ 2 + (V.card + 1)) (fun x _ => by
        have h1 := connBCost_le hFV x
        have h2 := card_creach_le hFV x V.card
        unfold connBCost at h1; unfold ccls; omega)
    simpa using this
  nlinarith
end ULHC
