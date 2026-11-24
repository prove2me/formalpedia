-- Prove2me | solution 1 for ULHC.TF.pred_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:50.835795+00:00
-- url     : https://prove2.me/submissions/d637d29c-035f-4a54-ab31-fc49e7563caf

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_mem_inc4
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {L : Finset Pt} {v : Pt} {e : Edge}
    (h : pred V F L v = some e) : (e.p = v ∨ e.q = v) ∧ Bwd V F L v e := by
  unfold pred at h
  have h2 := List.find?_some h
  exact ⟨mem_inc4.1 (List.mem_of_find?_eq_some h), by simpa using h2⟩
end ULHC.TF
