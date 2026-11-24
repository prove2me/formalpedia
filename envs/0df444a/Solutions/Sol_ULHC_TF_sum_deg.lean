-- Prove2me | solution 1 for ULHC.TF.sum_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:19.968805+00:00
-- url     : https://prove2.me/submissions/893391ea-dcd7-4667-85fc-50b6ad7b1103

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_deg_eq_card
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
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
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {S : Finset Pt} (hS : ∀ e : Edge, ¬ (e.p ∈ S ∧ e.q ∈ S)) (F : Finset Edge) :
    ∑ z ∈ S, deg F z = (F.filter (fun e => e.p ∈ S ∨ e.q ∈ S)).card := by
  classical
  simp_rw [deg_eq_card]
  rw [← card_biUnion]
  · congr 1
    ext e
    simp only [mem_biUnion, mem_filter]
    constructor
    · rintro ⟨z, hz, he, h | h⟩
      · exact ⟨he, Or.inl (h ▸ hz)⟩
      · exact ⟨he, Or.inr (h ▸ hz)⟩
    · rintro ⟨he, h | h⟩
      · exact ⟨_, h, he, Or.inl rfl⟩
      · exact ⟨_, h, he, Or.inr rfl⟩
  · intro x hx y hy hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro e h1 h2
    simp only [mem_filter] at h1 h2
    apply hS e
    rcases h1.2 with h1 | h1 <;> rcases h2.2 with h2 | h2
    · exact absurd (h1.symm.trans h2) hxy
    · exact ⟨h1 ▸ hx, h2 ▸ hy⟩
    · exact ⟨h2 ▸ hy, h1 ▸ hx⟩
    · exact absurd (h1.symm.trans h2) hxy
end ULHC.TF
