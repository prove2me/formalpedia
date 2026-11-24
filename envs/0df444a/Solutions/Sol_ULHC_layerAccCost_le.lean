-- Prove2me | solution 1 for ULHC.layerAccCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:49.41254+00:00
-- url     : https://prove2.me/submissions/6f879cf1-ca91-41cc-b43b-ef7d9b47d5cd

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
import Theorems.Thm_ULHC_card_nbr_le
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_TF_layerAcc_eq
import Theorems.Thm_ULHC_TF_layer_sub
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    ∀ k, layerAccCost V F k ≤ 13 * V.card + 55 * (V.card + 1) * k := by
  intro k
  induction k with
  | zero => simp [layerAccCost]
  | succ k ih =>
    simp only [layerAccCost]
    rw [layerAcc_eq]
    simp only
    set L := layer V F k
    have hL : L.card ≤ V.card := card_le_card (layer_sub k)
    have h1 : ∑ u ∈ L, (nbrCost + (nbr V F u).card) ≤ L.card * 49 := by
      have := Finset.sum_le_card_nsmul L (fun u => nbrCost + (nbr V F u).card) 49
        (fun u _ => by have := card_nbr_le V F u; unfold nbrCost; omega)
      simpa using this
    have h2 : (L.biUnion (nbr V F)).card ≤ L.card * 4 := by
      refine card_biUnion_le.trans ?_
      have := Finset.sum_le_card_nsmul L (fun u => (nbr V F u).card) 4
        (fun u _ => card_nbr_le V F u)
      simpa using this
    nlinarith
end ULHC
