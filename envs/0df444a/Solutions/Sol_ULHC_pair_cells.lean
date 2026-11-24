-- Prove2me | solution 1 for ULHC.pair_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:19:48.198952+00:00
-- url     : https://prove2.me/submissions/7ff822a1-791f-42b3-a42c-ebc8af5e5899

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_symmDiff_cells_frame
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_back_nb
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    symmDiff (cellE (nb c s)) (cellE c) =
      {back c s, lat1 c s, lat2 c s, front (nb c s) s, lat1 (nb c s) s, lat2 (nb c s) s} := by
  apply symmDiff_cells_frame (f := front c s)
  · rw [cellE_frame (nb c s) s, back_nb]
  · rw [cellE_frame c s]
  · obtain ⟨x, y⟩ := c
    cases s <;> simp [cellE, back, lat1, lat2, nb, sideEdge, Side.opp, bot, top, lft, rgt] <;>
      omega
  · obtain ⟨x, y⟩ := c
    cases s <;> simp [cellE, front, lat1, lat2, nb, sideEdge, bot, top, lft, rgt] <;> omega
end ULHC
