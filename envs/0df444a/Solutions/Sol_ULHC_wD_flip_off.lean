-- Prove2me | solution 1 for ULHC.wD_flip_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:07.000919+00:00
-- url     : https://prove2.me/submissions/3954527a-09b9-4cf9-9aac-e01e8c6fc14f

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_up_congr
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
theorem _root_.solution {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∉ cellE c) :
    wD (flip F c) H e = wD F H e := by
  have hm : e ∈ flip F c ↔ e ∈ F := by
    simp [flip, Finset.mem_symmDiff, he]
  unfold wD; rw [up_congr hm]; simp [hm]
end ULHC
