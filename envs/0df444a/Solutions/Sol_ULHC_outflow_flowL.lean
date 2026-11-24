-- Prove2me | solution 1 for ULHC.outflow_flowL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:26.517363+00:00
-- url     : https://prove2.me/submissions/494592ca-d576-409d-94c0-567764649650

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Theorems.Thm_ULHC_outflow_step
import Theorems.Thm_ULHC_outflow_add
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
namespace ULHC
theorem _root_.solution (u : Pt) (l : List Pt) (hc : List.IsChain Unit (u :: l)) (x : Pt) :
    outflow (flowL u l) x =
      (if x = u then 1 else 0) - (if x = (u :: l).getLast (by simp) then 1 else 0) := by
  induction l generalizing u with
  | nil =>
    simp only [flowL, outflow, List.getLast_singleton]
    by_cases h : x = u <;> simp [h]
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    have e1 : flowL u (v :: l) = fun e => stepFlow u v e + flowL v l e := rfl
    rw [e1, outflow_add, outflow_step u v x hc.1, ih v hc.2]
    rw [List.getLast_cons_cons]
    ring
end ULHC
