-- Prove2me | solution 1 for ULHC.suf_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:27.415917+00:00
-- url     : https://prove2.me/submissions/0ea282c8-f711-4a45-ab96-b680eddf4ae5

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_cellJ
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
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
namespace ULHC
theorem _root_.solution (hi : i < z.n) : endCell (suf z i) = endCell z := by
  unfold endCell; rw [suf_cellJ]; simp only [suf]; congr 1; omega
end ULHC
