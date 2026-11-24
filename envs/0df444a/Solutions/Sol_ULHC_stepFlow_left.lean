-- Prove2me | solution 1 for ULHC.stepFlow_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:00.433922+00:00
-- url     : https://prove2.me/submissions/9b6739b8-e638-4f37-99ea-b74d8727f6a6

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
theorem _root_.solution (u : Pt) :
    stepFlow u (u.1 - 1, u.2) = fun e => - oneE ⟨.h, (u.1 - 1, u.2)⟩ e := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega
end ULHC
