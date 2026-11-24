-- Prove2me | solution 1 for ULHC.candNCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:09.275832+00:00
-- url     : https://prove2.me/submissions/d762e61a-2a1b-47b1-b3b8-fa7fe79d6327

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_allStripsCost_le
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_card_allStrips
import Theorems.Thm_ULHC_card_candN_le
import Theorems.Thm_ULHC_card_cand_le
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (G : Finset Edge) : candNCost V G ≤ 300 * (V.card + 1) ^ 3 := by
  have hc := card_cand_le (V := V) G
  have hN := card_candN_le (V := V) G
  have h0 := allStripsCost_le V G
  have hf : (V.filter (IsCell V)).card ≤ V.card := card_filter_le _ _
  have h1 : ∑ u ∈ V.filter (IsCell V),
      (flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1) ≤
      V.card * (9 + 120 * (V.card + 1) ^ 2 + 4 * V.card) := by
    have := Finset.sum_le_card_nsmul (V.filter (IsCell V))
      (fun u => flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1)
      (9 + 120 * (V.card + 1) ^ 2 + 4 * V.card) (fun u _ => by
        have := allStripsCost_le V (flip G u)
        have := card_allStrips (V := V) (F := flip G u)
        unfold flipCost; omega)
    simp only [smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hf)
  unfold candNCost candCost Bd at *
  nlinarith
end ULHC
