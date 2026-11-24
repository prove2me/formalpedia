-- Prove2me | solution 1 for ULHC.DStep.parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:46:22.604741+00:00
-- url     : https://prove2.me/submissions/8dff8fd6-2cb8-4256-9774-6a0150f549c8

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_sidesIn_symmDiff
import Theorems.Thm_ULHC_sidesIn_single
import Theorems.Thm_ULHC_side_mem_cellE_iff
import Theorems.Thm_ULHC_nb_ne
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
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DStep
theorem _root_.solution {a d : Pt} {E : Finset Edge} (h : DStep V F a d E) (x : Pt) (hx : IsCell V x) :
    sidesIn E x % 2 = ((if x = a then 1 else 0) + (if x = d then 1 else 0)) % 2 := by
  cases h with
  | inner tf _ _ _ =>
    simp only [sidesIn_single, side_mem_cellE_iff]
    have := nb_ne a tf
    by_cases h1 : x = a <;> by_cases h2 : x = nb a tf <;> simp [h1, h2] <;> simp_all
  | outer _ tf t' _ _ n1 n2 _ _ =>
    rw [sidesIn_symmDiff]
    simp only [sidesIn_single, side_mem_cellE_iff]
    have e1 : x ≠ nb a tf := fun h => n1 (h ▸ hx)
    have e2 : x ≠ nb d t' := fun h => n2 (h ▸ hx)
    by_cases h1 : x = a <;> by_cases h2 : x = d <;> subst_vars <;> simp_all
end DStep
end ULHC
