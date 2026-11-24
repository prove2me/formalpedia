-- Prove2me | solution 1 for ULHC.unit_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:13.863702+00:00
-- url     : https://prove2.me/submissions/378fb34d-c34b-4a78-bf56-e29bc5323413

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
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
namespace ULHC
theorem _root_.solution {u v : Pt} (h : Unit u v) :
    v = (u.1 + 1, u.2) ∨ v = (u.1 - 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1, u.2 - 1) := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  unfold Unit at h
  simp only [Prod.mk.injEq] at h ⊢
  rcases abs_cases (u1 - v1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (u2 - v2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
end ULHC
