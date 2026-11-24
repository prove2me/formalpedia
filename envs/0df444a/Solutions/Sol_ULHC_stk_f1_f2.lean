-- Prove2me | solution 1 for ULHC.stk_f1_f2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:06.385332+00:00
-- url     : https://prove2.me/submissions/9a4c3253-879a-4651-97ac-27851d7b3580

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
theorem _root_.solution : front1 (nb c s) s ≠ front2 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [front1, front2, nb, ne_eq, Prod.mk.injEq] <;> omega
end ULHC
