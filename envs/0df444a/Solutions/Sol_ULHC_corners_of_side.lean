-- Prove2me | solution 1 for ULHC.corners_of_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:32.200782+00:00
-- url     : https://prove2.me/submissions/1fa623a3-8723-4b65-af06-4f0d4e59e3eb

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (P : Finset Pt)
    (h : (c ∈ P ↔ (c.1 + 1, c.2) ∈ P) ∧ (c ∈ P ↔ (c.1, c.2 + 1) ∈ P) ∧
      (c ∈ P ↔ (c.1 + 1, c.2 + 1) ∈ P)) : ¬ Cut P (sideEdge c s) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3⟩ := h
  unfold Cut
  cases s <;> simp only [sideEdge, bot, top, lft, rgt, Edge.q] <;> tauto
end ULHC
