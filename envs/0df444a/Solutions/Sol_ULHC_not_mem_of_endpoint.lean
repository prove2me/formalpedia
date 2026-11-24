-- Prove2me | solution 1 for ULHC.not_mem_of_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:56.115802+00:00
-- url     : https://prove2.me/submissions/f8a1b665-793c-4058-8b22-2d78a7b776b0

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
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
namespace ULHC
theorem _root_.solution {G : Finset Edge} {d' : Pt → ℕ} (hG : IsFactor V d' G)
    {e : Edge} {a : Pt} (ha : a ∉ V) (h : e.p = a ∨ e.q = a) : e ∉ G := by
  intro he
  obtain ⟨h1, h2⟩ := hG.1 e he
  rcases h with h | h <;> simp_all
end ULHC
