-- Prove2me | solution 1 for ULHC.ends_lat2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:01.385067+00:00
-- url     : https://prove2.me/submissions/330e3027-9ab6-4d47-a6e7-fdede8c5f536

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (lat2 c s) (back2 c s) (front2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, lat2, back2, front2, rgt, top, Edge.q]
end ULHC
