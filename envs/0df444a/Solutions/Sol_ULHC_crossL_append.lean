-- Prove2me | solution 1 for ULHC.crossL_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:26:51.702064+00:00
-- url     : https://prove2.me/submissions/2ae68f2b-2ae3-4777-b131-7bf663c81344

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
theorem _root_.solution (B : Finset Edge) (u : Pt) (l : List Pt) (d : Pt) :
    crossL B u (l ++ [d]) =
      crossL B u l + (if ∃ e ∈ B, Ends e ((u :: l).getLast (by simp)) d then 1 else 0) := by
  induction l generalizing u with
  | nil =>
    simp only [List.nil_append, crossL, List.getLast_singleton]
    by_cases h : ∃ e ∈ B, Ends e u d <;> simp only [h, ite_true, ite_false]
  | cons v l ih =>
    simp only [List.cons_append, crossL, ih v, List.getLast_cons_cons]
    by_cases h : ∃ e ∈ B, Ends e u v <;>
      by_cases h' : ∃ e ∈ B, Ends e ((v :: l).getLast (by simp)) d <;>
      simp only [h, h', ite_true, ite_false] <;> ring
end ULHC
