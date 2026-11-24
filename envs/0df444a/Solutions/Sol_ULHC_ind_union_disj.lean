-- Prove2me | solution 1 for ULHC.ind_union_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:22.402076+00:00
-- url     : https://prove2.me/submissions/348c8f1d-68fd-401a-8088-f8cefb58eadf

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
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
theorem _root_.solution {A B : Finset Edge} (h : Disjoint A B) (e : Edge) :
    ind (A ∪ B) e = ind A e + ind B e := by
  unfold ind
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> simp [ha, hb]
  exact Finset.disjoint_left.1 h ha hb
end ULHC
