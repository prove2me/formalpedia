-- Prove2me | solution 1 for ULHC.side_mem_cellE_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:10.2098+00:00
-- url     : https://prove2.me/submissions/2d1d2c65-35eb-4f62-9f34-16b65168bac1

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : sideEdge c s ∈ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [sideEdge, cellE, nb, bot, top, lft, rgt]
end ULHC
