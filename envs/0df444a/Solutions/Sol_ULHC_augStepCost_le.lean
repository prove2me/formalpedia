-- Prove2me | solution 1 for ULHC.augStepCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:13.401956+00:00
-- url     : https://prove2.me/submissions/663410da-5957-4a99-b8ca-f108865bf113

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
import Theorems.Thm_ULHC_length_layersBelow
import Theorems.Thm_ULHC_walkCost_le
import Theorems.Thm_ULHC_layerAccCost_le
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
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
    augStepCost V F ≤ 130 * (V.card + 1) ^ 2 := by
  have h0 := layerAccCost_le V F V.card
  unfold augStepCost
  rw [layerAcc_eq]
  simp only
  set L := layer V F V.card
  have hL : L.card ≤ V.card := card_le_card (layer_sub _)
  have hfl : (L.filter (fun w => ¬ Black w ∧ deg F w < 2)).card ≤ V.card :=
    (card_filter_le _ _).trans hL
  have hw : ∀ w, walkCost V F (layersBelow V F V.card) w F ≤ 45 * (V.card + 1) := fun w => by
    have := walkCost_le V F (layersBelow V F V.card) w F
    rwa [length_layersBelow] at this
  simp only [sum_const, smul_eq_mul]
  unfold pickCost degCost
  have hsq : 55 * (V.card + 1) * V.card ≤ 55 * (V.card + 1) ^ 2 := by
    rw [Nat.mul_assoc, pow_two]
    exact Nat.mul_le_mul_left 55 (Nat.mul_le_mul_left (V.card + 1) (Nat.le_succ _))
  have hlin : V.card + 1 ≤ (V.card + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_self _
  rcases pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with _ | w
  · simp only; omega
  · simp only; have := hw w; omega
end ULHC
