-- Prove2me | solution 1 for ULHC.ind_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:05:54.843965+00:00
-- url     : https://prove2.me/submissions/25d2bac0-99d9-4299-89b9-5678abb7c440

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
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
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) (g : Edge) :
    ind (F.erase e) g + (if g = e then 1 else 0) = ind F g := by
  unfold ind
  by_cases h : g = e
  · subst h; simp [he]
  · simp [h, Finset.mem_erase]
end ULHC
