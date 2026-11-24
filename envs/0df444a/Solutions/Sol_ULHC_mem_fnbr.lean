-- Prove2me | solution 1 for ULHC.mem_fnbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:23.359038+00:00
-- url     : https://prove2.me/submissions/41192616-cff7-48e4-9a1b-e654137cc376

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_TF_mem_inc4
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution {u v : Pt} : v ∈ fnbr F u ↔ ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ other e u = v := by
  simp [fnbr, TF.mem_inc4]
  constructor
  · rintro ⟨e, ⟨h1, h2⟩, h3⟩; exact ⟨e, h2, h1, h3⟩
  · rintro ⟨e, h2, h1, h3⟩; exact ⟨e, ⟨h1, h2⟩, h3⟩
end ULHC
