-- Prove2me | solution 1 for ULHC.creachCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:28:21.556837+00:00
-- url     : https://prove2.me/submissions/d2212946-a405-4a1f-8eed-8eb3cd99aa24

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_card_fnbr_le
import Theorems.Thm_ULHC_card_creach_le
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    ∀ k, creachCost F x k ≤ 1 + 29 * (V.card + 1) * k := by
  intro k
  induction k with
  | zero => simp [creachCost]
  | succ k ih =>
    simp only [creachCost]
    set C := creach F x k
    have hC : C.card ≤ V.card + 1 := card_creach_le hFV x k
    have h1 : ∑ u ∈ C, (fnbrCost + (fnbr F u).card) ≤ C.card * 24 := by
      have := Finset.sum_le_card_nsmul C (fun u => fnbrCost + (fnbr F u).card) 24
        (fun u _ => by have := card_fnbr_le F u; unfold fnbrCost; omega)
      simpa using this
    have h2 : (C.biUnion (fnbr F)).card ≤ C.card * 4 := by
      refine card_biUnion_le.trans ?_
      have := Finset.sum_le_card_nsmul C (fun u => (fnbr F u).card) 4
        (fun u _ => card_fnbr_le F u)
      simpa using this
    nlinarith
end ULHC
