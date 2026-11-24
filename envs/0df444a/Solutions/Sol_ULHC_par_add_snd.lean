-- Prove2me | solution 1 for ULHC.par_add_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:02.1007+00:00
-- url     : https://prove2.me/submissions/e03445d9-0d43-4b65-a5fc-cd1181f840d8

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
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
theorem _root_.solution (c : Pt) : par (c.1, c.2 + 1) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega
end ULHC
