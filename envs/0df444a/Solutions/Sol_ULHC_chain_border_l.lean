-- Prove2me | solution 1 for ULHC.chain_border_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:19:54.573183+00:00
-- url     : https://prove2.me/submissions/f3eed55a-accf-4fe8-9503-c861fb56f4a7

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_separation
import Theorems.Thm_ULHC_sidesIn_EB_even_l
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hs : Solid V) (hF : Deg2 V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ EB V F c0) := by
  apply separation (EB V F c0) hs (sidesIn_EB_even_l hF c0 hC) hF.1
  · intro e he
    simp only [EB, Finset.mem_filter] at he
    exact he.2.1.2.1
  · exact hconn
end ULHC
