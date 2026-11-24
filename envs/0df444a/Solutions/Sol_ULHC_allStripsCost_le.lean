-- Prove2me | solution 1 for ULHC.allStripsCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:45.158302+00:00
-- url     : https://prove2.me/submissions/496174b6-b7d8-4836-989d-f05b088da5ad

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_stripScanCost_le
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    allStripsCost V F ≤ 120 * (V.card + 1) ^ 2 := by
  unfold allStripsCost
  have hf : (V.filter (IsCell V)).card ≤ V.card := card_filter_le _ _
  have hs : sidesF.card = 4 := by decide
  have h1 : ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) ≤
      V.card * (4 * (21 * (V.card + 1) + 4) + 5) := by
    have := Finset.sum_le_card_nsmul (V.filter (IsCell V))
      (fun c => ∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) (4 * (21 * (V.card + 1) + 4) + 5)
      (fun c _ => by
        have := Finset.sum_le_card_nsmul sidesF (fun s => stripLenCost V F c s + 2)
          (21 * (V.card + 1) + 4) (fun s _ => by
            have := stripScanCost_le V F c s V.card 0; unfold stripLenCost; omega)
        simp only [hs, smul_eq_mul] at this
        omega)
    simp only [smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hf)
  simp only [sum_const, smul_eq_mul]
  nlinarith
end ULHC
