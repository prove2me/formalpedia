-- Prove2me | solution 1 for ULHC.cut_even_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:11.319862+00:00
-- url     : https://prove2.me/submissions/12cb42de-40db-41cb-a506-bf7772957b87

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
import Theorems.Thm_ULHC_Conn_of_edge
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cut_sides_even
import Theorems.Thm_ULHC_mem_GE
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (S : Finset Pt)
    (hS : ∀ x y, Conn F x y → (x ∈ S ↔ y ∈ S)) :
    let B := (GE V).filter (Cut S)
    (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧ (∀ f ∈ B, f ∉ F) ∧
      ∀ f, f ∈ B ↔ IsEdge V f ∧ Cut S f := by
  intro B
  refine ⟨cut_sides_even S B (fun f => by simp [B, Finset.mem_filter, mem_GE]), ?_, ?_⟩
  · intro f hf hfF
    simp only [B, Finset.mem_filter] at hf
    have := hS _ _ (Conn.of_edge hfF)
    unfold Cut at hf
    tauto
  · intro f; simp [B, Finset.mem_filter, mem_GE]
end ULHC
