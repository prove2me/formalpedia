-- Prove2me | solution 1 for ULHC.exists_inc_of_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:52.805541+00:00
-- url     : https://prove2.me/submissions/baf3a306-2dd0-4839-9bca-071fecef8c9e

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
theorem _root_.solution {F : Finset Edge} {y : Pt} (h : 1 ≤ deg F y) :
    ∃ e ∈ F, e.p = y ∨ e.q = y := by
  unfold deg ind at h
  by_cases h1 : eR y ∈ F
  · exact ⟨_, h1, Or.inl (by simp [eR])⟩
  by_cases h2 : eL y ∈ F
  · exact ⟨_, h2, Or.inr (by simp [eL, Edge.q])⟩
  by_cases h3 : eU y ∈ F
  · exact ⟨_, h3, Or.inl (by simp [eU])⟩
  by_cases h4 : eD y ∈ F
  · exact ⟨_, h4, Or.inr (by simp [eD, Edge.q])⟩
  simp [h1, h2, h3, h4] at h
end ULHC
