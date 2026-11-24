-- Prove2me | solution 1 for ULHC.corners_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:19.086334+00:00
-- url     : https://prove2.me/submissions/4ae53eb4-b5b4-4bcd-8417-871ffbb7bbe4

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
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
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution {c : Pt} (hc : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ front1 c s ∈ V := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases s <;> exact ⟨by simpa [back1] using ‹_›, by simpa [front1] using ‹_›⟩
end ULHC
