-- Prove2me | solution 1 for ULHC.TF.mem_inc4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:53.504884+00:00
-- url     : https://prove2.me/submissions/7586302b-eeca-4191-9a2f-403bb989f27e

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
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
theorem _root_.solution {e : Edge} {z : Pt} : e ∈ inc4 z ↔ e.p = z ∨ e.q = z := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨z1, z2⟩ := z
  cases d <;> simp [inc4, eR, eL, eU, eD, Edge.q] <;> constructor <;> intro h <;> omega
end ULHC.TF
