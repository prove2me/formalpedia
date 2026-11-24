-- Prove2me | solution 1 for ULHC.stepFlow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:59.041895+00:00
-- url     : https://prove2.me/submissions/7bb0251f-5edc-4a4a-bb6f-f397cd4fa5e3

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
theorem _root_.solution {u v : Pt} {e : Edge} (h : stepFlow u v e ≠ 0) :
    (e.p = u ∧ e.q = v) ∨ (e.p = v ∧ e.q = u) := by
  unfold stepFlow at h
  by_contra hc
  push Not at hc
  rw [if_neg (fun h' => hc.1 h'.1 h'.2), if_neg (fun h' => hc.2 h'.1 h'.2)] at h
  simp at h
end ULHC
