-- Prove2me | solution 1 for ULHC.mem_sidesL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:35.031593+00:00
-- url     : https://prove2.me/submissions/e839ca98-25b2-436f-a952-e9a0249d9b26

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
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
open Finset
namespace ULHC
theorem _root_.solution (tf : Side) : tf ∈ sidesL := by cases tf <;> simp [sidesL]
end ULHC
