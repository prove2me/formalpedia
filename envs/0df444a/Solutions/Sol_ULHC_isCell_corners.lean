-- Prove2me | solution 1 for ULHC.isCell_corners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:38.006806+00:00
-- url     : https://prove2.me/submissions/dc3d82db-5e97-4f08-bc45-bb54a17f50ad

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
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
theorem _root_.solution {V : Finset Pt} {c : Pt} (h : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ back2 c s ∈ V ∧ front1 c s ∈ V ∧ front2 c s ∈ V := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases s <;> simp only [back1, back2, front1, front2] <;> exact ⟨by assumption, by assumption,
    by assumption, by assumption⟩
end ULHC
