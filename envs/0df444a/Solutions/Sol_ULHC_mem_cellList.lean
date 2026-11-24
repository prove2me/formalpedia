-- Prove2me | solution 1 for ULHC.mem_cellList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:58:50.718278+00:00
-- url     : https://prove2.me/submissions/6f2437ca-30f3-4810-b7c4-c43ad262000d

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
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
theorem _root_.solution {V : Finset Pt} {d : Pt} : d ∈ cellList V ↔ d ∈ V ∧ IsCell V d := by
  unfold cellList
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; exact hx
  · intro h; exact ⟨toLex d, ⟨d, h, rfl⟩, rfl⟩
end ULHC
