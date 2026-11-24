-- Prove2me | solution 1 for ULHC.outflow_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:54.498558+00:00
-- url     : https://prove2.me/submissions/1f14bedb-bdf3-4006-8214-c589597ed2b8

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Theorems.Thm_ULHC_unit_cases
import Theorems.Thm_ULHC_stepFlow_right
import Theorems.Thm_ULHC_stepFlow_left
import Theorems.Thm_ULHC_stepFlow_up
import Theorems.Thm_ULHC_stepFlow_down
import Theorems.Thm_ULHC_outflow_oneE_h
import Theorems.Thm_ULHC_outflow_oneE_v
import Theorems.Thm_ULHC_outflow_neg
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
theorem _root_.solution (u v x : Pt) (h : Unit u v) :
    outflow (stepFlow u v) x = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  obtain ⟨u1, u2⟩ := u
  rcases unit_cases h with h' | h' | h' | h' <;> subst h'
  · rw [stepFlow_right, outflow_oneE_h]
  · rw [stepFlow_left, outflow_neg, outflow_oneE_h]
    simp only [sub_add_cancel]; ring
  · rw [stepFlow_up, outflow_oneE_v]
  · rw [stepFlow_down, outflow_neg, outflow_oneE_v]
    simp only [sub_add_cancel]; ring
end ULHC
