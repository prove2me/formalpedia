-- Prove2me | solution 1 for ULHC.symmDiff_cells_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:17:25.871031+00:00
-- url     : https://prove2.me/submissions/33c86b62-32e4-4a1d-965c-01e0a01aa4fa

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
theorem _root_.solution {f x1 x2 x3 y1 y2 y3 : Edge} {E1 E2 : Finset Edge}
    (hE1 : E1 = {f, y1, y2, y3}) (hE2 : E2 = {x1, f, x2, x3})
    (hx : ∀ x ∈ ({x1, x2, x3} : Finset Edge), x ∉ E1)
    (hy : ∀ y ∈ ({y1, y2, y3} : Finset Edge), y ∉ E2) :
    symmDiff E1 E2 = {x1, x2, x3, y1, y2, y3} := by
  subst hE1 hE2
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hx hy
  constructor
  · rintro (⟨h | h | h | h, hn⟩ | ⟨h | h | h | h, hn⟩)
    · exact absurd (Or.inr (Or.inl h)) hn
    all_goals first
      | (subst h; tauto)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> tauto
end ULHC
