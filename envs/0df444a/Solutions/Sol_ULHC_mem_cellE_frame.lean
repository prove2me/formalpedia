-- Prove2me | solution 1 for ULHC.mem_cellE_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:06.757321+00:00
-- url     : https://prove2.me/submissions/15eedf82-5123-4c61-8c3c-babd815ec8e0

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellE_frame
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (g : Edge) :
    g ∈ cellE c ↔ g = back c s ∨ g = front c s ∨ g = lat1 c s ∨ g = lat2 c s := by
  rw [cellE_frame c s]; simp only [Finset.mem_insert, Finset.mem_singleton]
end ULHC
