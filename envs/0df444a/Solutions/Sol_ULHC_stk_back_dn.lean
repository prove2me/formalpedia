-- Prove2me | solution 1 for ULHC.stk_back_dn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:58.293865+00:00
-- url     : https://prove2.me/submissions/dae9c6c3-579c-4f7a-a08a-3e721177290f

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
theorem _root_.solution : back c s ∉ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, back, sideEdge, Side.opp, nb, bot, top, lft, rgt,
    Finset.mem_insert, Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq,
    reduceCtorEq, true_and, and_true, false_and, or_false, false_or] <;> omega
end ULHC
