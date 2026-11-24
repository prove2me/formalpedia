-- Prove2me | solution 1 for ULHC.sidesIn_EB_even_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:18:36.109782+00:00
-- url     : https://prove2.me/submissions/6deeb116-0862-4432-ab2e-36b8a9e516ab

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_interCount_even_l
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_side_mem_cellE
import Theorems.Thm_ULHC_on_chain_of_side
import Theorems.Thm_ULHC_side_mem_cellE_nb
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_cells
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hF : Deg2 V F) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∀ c, IsCell V c → sidesIn (EB V F c0) c % 2 = 0 := by
  intro c hc
  have hGE : ∀ s : Side, sideEdge c s ∈ GE V := by
    intro s; rw [mem_GE]
    obtain ⟨x, y⟩ := c
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  by_cases hin : c ∈ chainCells V F c0
  · have hiff : ∀ s : Side, sideEdge c s ∈ EB V F c0 ↔ Inter V F (sideEdge c s) := by
      intro s
      simp only [EB, Finset.mem_filter]
      constructor
      · exact fun h => h.2.1
      · exact fun h => ⟨hGE s, h, c, hin, side_mem_cellE c s⟩
    have hTn : ∀ s, Inter V F (sideEdge c s) → IsCell V (nb c s) → NotTypeIII V F (nb c s) := by
      intro s hI hcell
      apply hC
      simp only [chainCells, Finset.mem_filter] at hin ⊢
      exact ⟨mem_cells.2 hcell, hin.2.tail ⟨hc, hcell, _, hI, side_mem_cellE c s,
        side_mem_cellE_nb c s⟩⟩
    have := interCount_even_l hF hc (hC c hin) hTn
    unfold sidesIn interCount ind at *
    have hb := hiff .b; have ht := hiff .t; have hl := hiff .l; have hr := hiff .r
    simp only [sideEdge] at hb ht hl hr
    simp only [hb, ht, hl, hr]
    exact this
  · have hno : ∀ s : Side, sideEdge c s ∉ EB V F c0 := fun s h =>
      hin (on_chain_of_side hc (side_mem_cellE c s) h)
    unfold sidesIn ind
    have hb := hno .b; have ht := hno .t; have hl := hno .l; have hr := hno .r
    simp only [sideEdge] at hb ht hl hr
    simp [hb, ht, hl, hr]
end ULHC
