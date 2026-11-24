-- Prove2me | solution 1 for ULHC.par_add_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:58.7438+00:00
-- url     : https://prove2.me/submissions/c95cd25a-706e-42c8-9a38-92c6c9d41b84

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
theorem _root_.solution (c : Pt) : par (c.1 + 1, c.2) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega
end ULHC
