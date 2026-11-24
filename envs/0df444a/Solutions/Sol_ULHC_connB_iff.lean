-- Prove2me | solution 1 for ULHC.connB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:01.300027+00:00
-- url     : https://prove2.me/submissions/1b12204e-34fa-45ea-8a9e-0939a415dfb0

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_ccls_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) {x y : Pt} (hx : x ∈ V) (hy : y ∈ V) :
    connB V F x y = true ↔ Conn F x y := by
  simp only [connB, decide_eq_true_eq, ccls_eq hFV hx, cls, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
end ULHC
