-- Prove2me | solution 1 for ULHC.midB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:01:36.53922+00:00
-- url     : https://prove2.me/submissions/223c2986-077c-4944-916d-f087a91c5c33

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
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
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution {b : StripSpec} {z : Pt} : midB b z = true ↔ IsMid b.c b.s (b.n - 2) z := by
  simp only [midB, IsMid, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, h1, h2⟩; exact ⟨j, h1, hj, h2⟩
  · rintro ⟨j, h1, hj, h2⟩; exact ⟨j, hj, h1, h2⟩
end ULHC
