-- Prove2me | solution 1 for ULHC.suf_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:10.380628+00:00
-- url     : https://prove2.me/submissions/b0f8ece1-2305-4d3c-a3e0-f3fea5601c2b

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_cellJ
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
namespace ULHC
theorem _root_.solution (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j)) :
    ∀ j < (suf z i).n, IsCell V (cellJ (suf z i).c (suf z i).s j) := by
  intro j hj; rw [suf_cellJ]; simp only [suf] at hj; exact hc _ (by omega)
end ULHC
