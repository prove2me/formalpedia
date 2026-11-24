-- Prove2me | solution 1 for ULHC.nb_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:45.794269+00:00
-- url     : https://prove2.me/submissions/6c7afc9e-0bec-4c36-8b71-a147aa2311ee

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
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
theorem _root_.solution (c : Pt) (tf : Side) : c ≠ nb c tf := by
  obtain ⟨p, q⟩ := c; cases tf <;> simp [nb] <;> omega
end ULHC
