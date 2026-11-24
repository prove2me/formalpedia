-- Prove2me | solution 1 for ULHC.cell_of_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:33:25.745686+00:00
-- url     : https://prove2.me/submissions/e7586526-15bb-4270-947d-3fa7e254f6a1

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_cellE_iff
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution {d : Pt} {tf : Side} (h : sideEdge c tf ∈ cellE d) : d = c ∨ d = nb c tf := by
  rw [mem_cellE_iff] at h
  obtain ⟨x, y⟩ := c
  cases tf <;> rcases h with h | h <;>
    simp only [sideEdge, bot, top, lft, rgt, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at h <;>
    subst h <;> simp [nb]
end ULHC
