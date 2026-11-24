-- Prove2me | solution 1 for ULHC.flowL_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:22.445312+00:00
-- url     : https://prove2.me/submissions/9c589d63-65a4-46d3-9278-84a29f7cf4ae

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Theorems.Thm_ULHC_stepFlow_ne_zero
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
theorem _root_.solution {u : Pt} {l : List Pt} {e : Edge} (h : flowL u l e ≠ 0) :
    e.p ∈ u :: l ∧ e.q ∈ u :: l := by
  induction l generalizing u with
  | nil => simp [flowL] at h
  | cons v l ih =>
    simp only [flowL] at h
    by_cases h1 : stepFlow u v e = 0
    · rw [h1, zero_add] at h
      obtain ⟨h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
    · rcases stepFlow_ne_zero h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> simp [h2, h3]
end ULHC
