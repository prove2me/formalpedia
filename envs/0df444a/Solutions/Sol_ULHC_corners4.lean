-- Prove2me | solution 1 for ULHC.corners4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:52.162278+00:00
-- url     : https://prove2.me/submissions/ea7ea096-3dcd-4fad-a33f-6a34271cc5bc

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
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
theorem _root_.solution {V : Finset Pt} {c : Pt} (hc : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ back2 c s ∈ V ∧ front1 c s ∈ V ∧ front2 c s ∈ V := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases s <;> simp only [back1, back2, front1, front2] <;> exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
end ULHC
