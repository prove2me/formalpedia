-- Prove2me | solution 1 for ULHC.wD_flip_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:14.699802+00:00
-- url     : https://prove2.me/submissions/dca39801-97ed-4b3a-8a18-0cefa6aa0bd7

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
theorem _root_.solution {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∈ cellE c) :
    wD (flip F c) H e - wD F H e = - (if up F e then 2 else -2) := by
  have hm : e ∈ flip F c ↔ e ∉ F := by
    simp [flip, Finset.mem_symmDiff, he]
  have hu : up (flip F c) e = ! up F e := by
    unfold up inE1
    cases e.d <;> cases par e.lo <;> by_cases h : e ∈ F <;> simp [hm, h]
  unfold wD; rw [hu]
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> cases up F e <;> simp [hm, h1, h2, wb]
end ULHC
