-- Prove2me | solution 1 for ULHC.len_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:08:35.013508+00:00
-- url     : https://prove2.me/submissions/4f75cb06-1766-4bf7-91a2-198044e33af1

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_inj
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {c : Pt} {s : Side} {n : ℕ}
    (hc : ∀ j < n, IsCell V (cellJ c s j)) : n ≤ V.card := by
  have hsub : (range n).image (cellJ c s) ⊆ V := by
    intro z hz
    simp only [mem_image, mem_range] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    exact (hc j hj).1
  have := card_le_card hsub
  rwa [card_image_of_injective _ (fun i j h => cellJ_inj c s h), card_range] at this
end ULHC
