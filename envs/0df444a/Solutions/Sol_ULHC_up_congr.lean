-- Prove2me | solution 1 for ULHC.up_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:02.434514+00:00
-- url     : https://prove2.me/submissions/f33c134c-7626-4d36-a9e1-fe72d6a13bce

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
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
theorem _root_.solution {F F' : Finset Edge} {e : Edge} (h : e ∈ F ↔ e ∈ F') : up F e = up F' e := by
  unfold up inE1; simp [h]
end ULHC
