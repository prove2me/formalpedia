-- Prove2me | solution 1 for ULHC.rot_supp_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:34.20756+00:00
-- url     : https://prove2.me/submissions/a31ca307-f7a2-476c-98b2-242695bb22ea

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
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
theorem _root_.solution {f : Edge → ℤ} {L : List Pt} (h : ∀ e, f e ≠ 0 → e.p ∈ L) :
    Supp (edgesAt L) (rot f) := by
  intro e he
  have : f e = 0 := by
    by_contra hne
    apply he
    obtain ⟨d, p⟩ := e
    have hp := h _ hne
    simp only [edgesAt, Finset.mem_biUnion, List.mem_toFinset]
    refine ⟨p, hp, ?_⟩
    cases d <;> simp [eR, eU]
  unfold rot; cases e.d <;> simp [this]
end ULHC
