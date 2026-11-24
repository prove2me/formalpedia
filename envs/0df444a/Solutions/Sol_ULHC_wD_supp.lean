-- Prove2me | solution 1 for ULHC.wD_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:50.582454+00:00
-- url     : https://prove2.me/submissions/c8f77e7a-f57e-468c-bb17-85ba7801312e

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
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
theorem _root_.solution (F H : Finset Edge) : Supp (symmDiff F H) (wD F H) := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  unfold wD wb
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> simp_all
end ULHC
