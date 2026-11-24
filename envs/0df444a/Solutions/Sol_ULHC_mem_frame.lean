-- Prove2me | solution 1 for ULHC.mem_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:06.839797+00:00
-- url     : https://prove2.me/submissions/52d784bb-745f-4ee3-9bc7-f88ed23e4771

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
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
namespace ULHC
theorem _root_.solution (z : Pt) (tf : Side) {y : Edge}
    (hy : y = lat1 z tf ∨ y = lat2 z tf ∨ y = back z tf ∨ y = front z tf) : y ∈ cellE z := by
  rw [cellE_frame z tf]; rcases hy with rfl | rfl | rfl | rfl <;> simp
end ULHC
