-- Prove2me | solution 1 for ULHC.stk_b2_f1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:57.61089+00:00
-- url     : https://prove2.me/submissions/dc570648-1850-441b-94e2-af3d52284771

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : back2 c s ≠ front1 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [back2, front1, ne_eq, Prod.mk.injEq] <;> omega
end ULHC
