-- Prove2me | solution 1 for ULHC.deg_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:16.789884+00:00
-- url     : https://prove2.me/submissions/1ba3577c-2d80-4cb8-90db-e139b0c268ed

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
theorem _root_.solution {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge}
    (hF : IsFactor V d F) {p : Pt} (hp : p ∉ V) : deg F p = 0 := by
  obtain ⟨x, y⟩ := p
  have h : ∀ e ∈ F, e.p ∈ V ∧ e.q ∈ V := fun e he => hF.1 e he
  have n1 : eR (x, y) ∉ F := fun he => hp (h _ he).1
  have n2 : eL (x, y) ∉ F := fun he => by
    have := (h _ he).2; simp [eL] at this; exact hp this
  have n3 : eU (x, y) ∉ F := fun he => hp (h _ he).1
  have n4 : eD (x, y) ∉ F := fun he => by
    have := (h _ he).2; simp [eD] at this; exact hp this
  simp [deg, ind, n1, n2, n3, n4]
end ULHC
