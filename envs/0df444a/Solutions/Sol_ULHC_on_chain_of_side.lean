-- Prove2me | solution 1 for ULHC.on_chain_of_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:03.312407+00:00
-- url     : https://prove2.me/submissions/ee2e8617-1486-4795-a9db-fcaca65f9ab3

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
theorem _root_.solution {c0 w : Pt} {e : Edge} (hw : IsCell V w) (he : e ∈ cellE w)
    (hB : e ∈ EB V F c0) : w ∈ chainCells V F c0 := by
  simp only [EB, Finset.mem_filter] at hB
  obtain ⟨_, hI, c', hc', hec'⟩ := hB
  simp only [chainCells, Finset.mem_filter] at hc' ⊢
  refine ⟨mem_cells.2 hw, hc'.2.tail ⟨mem_cells.1 hc'.1, hw, e, hI, hec', he⟩⟩
end ULHC
