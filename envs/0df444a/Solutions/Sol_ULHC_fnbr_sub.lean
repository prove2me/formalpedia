-- Prove2me | solution 1 for ULHC.fnbr_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:19.666033+00:00
-- url     : https://prove2.me/submissions/d5be3a8f-f170-42bd-a72d-539bee857f00

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_other_inc
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (u : Pt) : fnbr F u ⊆ V := by
  intro z hz
  simp only [fnbr, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hz
  obtain ⟨e, ⟨_, he⟩, rfl⟩ := hz
  rcases (other_inc (e := e) (y := u)) with h | h
  · rw [← h]; exact (hFV e he).1
  · rw [← h]; exact (hFV e he).2
end ULHC
