-- Prove2me | solution 1 for ULHC.stepFlow_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:03.10943+00:00
-- url     : https://prove2.me/submissions/b699ebbb-7943-4056-b82f-2e26290d9f98

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
theorem _root_.solution (u : Pt) : stepFlow u (u.1, u.2 + 1) = oneE ⟨.v, u⟩ := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega
end ULHC
