-- Prove2me | solution 1 for ULHC.inc_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:10.451071+00:00
-- url     : https://prove2.me/submissions/fdd7e882-7249-4682-8377-30ca5f88475b

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
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
theorem _root_.solution (e : Edge) (y : Pt) :
    (if eR y = e then 1 else 0) + (if eU y = e then 1 else 0) + (if eL y = e then 1 else 0) +
      (if eD y = e then 1 else 0) = (if e.p = y ∨ e.q = y then 1 else 0 : ℕ) := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨y1, y2⟩ := y
  cases d <;> simp only [eR, eU, eL, eD, Edge.q, Edge.mk.injEq, Prod.mk.injEq,
    reduceCtorEq, false_and, true_and, ite_false] <;> split_ifs <;> omega
end ULHC
