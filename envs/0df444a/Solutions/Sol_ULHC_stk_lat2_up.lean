-- Prove2me | solution 1 for ULHC.stk_lat2_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:56.581856+00:00
-- url     : https://prove2.me/submissions/f981f4f5-c1f2-479c-a755-985bb2deab32

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
theorem _root_.solution : lat2 (nb c s) s ∉ cellE c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, lat2, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega
end ULHC
