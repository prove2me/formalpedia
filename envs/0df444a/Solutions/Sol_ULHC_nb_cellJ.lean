-- Prove2me | solution 1 for ULHC.nb_cellJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:41.603832+00:00
-- url     : https://prove2.me/submissions/2f60a31a-20f7-498d-999d-1555b8a2b86b

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (j : ℕ) : nb (cellJ c s j) s = cellJ c s (j + 1) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [nb, cellJ] <;> ring
end ULHC
