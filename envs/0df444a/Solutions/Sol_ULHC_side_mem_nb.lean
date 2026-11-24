-- Prove2me | solution 1 for ULHC.side_mem_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:08.760091+00:00
-- url     : https://prove2.me/submissions/ec57926d-aba1-400d-8dbd-62ee4c0bd54f

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
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
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE (nb c tf) := by
  obtain ⟨x, y⟩ := c
  cases tf <;> simp [cellE, sideEdge, nb, bot, top, lft, rgt]
end ULHC
