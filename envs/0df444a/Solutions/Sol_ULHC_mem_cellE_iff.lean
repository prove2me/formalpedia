-- Prove2me | solution 1 for ULHC.mem_cellE_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:31:23.539728+00:00
-- url     : https://prove2.me/submissions/f047910d-d682-488e-bcd3-10fd95670b77

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_hi_eq_iff
import Theorems.Thm_ULHC_lo_eq_iff
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
theorem _root_.solution (e : Edge) (c : Pt) : e ∈ cellE c ↔ (e.hi = c ∨ e.lo = c) := by
  rw [hi_eq_iff, lo_eq_iff]; simp [cellE]; tauto
end ULHC
