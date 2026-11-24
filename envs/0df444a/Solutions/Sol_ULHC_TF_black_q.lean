-- Prove2me | solution 1 for ULHC.TF.black_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:59.896144+00:00
-- url     : https://prove2.me/submissions/2c2a973e-41cb-412c-b583-78111a367a42

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
theorem _root_.solution (e : Edge) : Black e.q ↔ ¬ Black e.p := by
  obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [Black, Edge.q] <;> omega
end ULHC.TF
