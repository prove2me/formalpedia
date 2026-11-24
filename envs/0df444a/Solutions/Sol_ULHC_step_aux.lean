-- Prove2me | solution 1 for ULHC.step_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:27.340806+00:00
-- url     : https://prove2.me/submissions/50cec825-c155-464a-b0ca-971581b8f7b1

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
theorem _root_.solution (a b : ℤ) (u s : Bool) (h : b - a = wb s u) :
    (if u then b - a else a - b) = if s then 2 else 0 := by
  cases u <;> cases s <;> simp [wb] at h ⊢ <;> linarith
end ULHC
