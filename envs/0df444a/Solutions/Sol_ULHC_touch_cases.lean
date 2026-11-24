-- Prove2me | solution 1 for ULHC.touch_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:37:35.842609+00:00
-- url     : https://prove2.me/submissions/5611ec60-bcdf-4437-832a-9c00c212e665

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {q d : Pt} (s : Side) {x : Edge} (h1 : x ∈ cellE q) (h2 : x ∈ cellE d) :
    q = d ∨ q = nb d s ∨ q = nb d s.opp ∨ q = nb d (latA s) ∨ q = nb d (latB s) := by
  rw [cellE_frame d s] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  rcases h2 with rfl | rfl | rfl | rfl
  · rcases cell_of_side d (tf := s.opp) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases cell_of_side d (tf := s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [lat1_eq] at h1
    rcases cell_of_side d (tf := latA s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [lat2_eq] at h1
    rcases cell_of_side d (tf := latB s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
end ULHC
