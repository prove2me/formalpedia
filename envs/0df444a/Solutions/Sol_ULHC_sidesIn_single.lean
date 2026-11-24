-- Prove2me | solution 1 for ULHC.sidesIn_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:42.014701+00:00
-- url     : https://prove2.me/submissions/0cda5acf-1b16-4906-b9e9-4cde0557e99e

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
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
open Finset Classical
namespace ULHC
theorem _root_.solution (e : Edge) (x : Pt) :
    sidesIn {e} x = if e ∈ cellE x then 1 else 0 := by
  obtain ⟨d, p⟩ := e
  obtain ⟨a, b⟩ := x
  unfold sidesIn ind cellE
  cases d <;>
    simp only [bot, top, lft, rgt, Finset.mem_singleton, Finset.mem_insert, Edge.mk.injEq,
      reduceCtorEq, false_and, or_false, false_or, true_and] <;>
    split_ifs <;> simp_all [Prod.ext_iff] <;> grind
end ULHC
