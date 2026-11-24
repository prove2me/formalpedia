-- Prove2me | solution 1 for ULHC.outflow_oneE_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:08.924686+00:00
-- url     : https://prove2.me/submissions/162cc353-ab6a-48a9-b512-eece15bbc133

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
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
theorem _root_.solution (a : Pt) (x : Pt) :
    outflow (oneE ⟨.h, a⟩) x = (if x = a then 1 else 0) - (if x = (a.1 + 1, a.2) then 1 else 0) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨x1, x2⟩ := x
  simp only [outflow, oneE, eR, eU, eL, eD, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq,
    false_and, ite_false, sub_zero, add_zero]
  by_cases h1 : x1 = a1 <;> by_cases h2 : x2 = a2 <;> by_cases h3 : x1 = a1 + 1 <;>
    (simp [h1, h2, h3]; try omega)
end ULHC
