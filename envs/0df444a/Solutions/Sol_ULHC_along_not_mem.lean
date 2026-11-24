-- Prove2me | solution 1 for ULHC.along_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:03:04.911051+00:00
-- url     : https://prove2.me/submissions/86d15a62-4c4f-4665-a511-b90386b8cf5d

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) {i i' : ℕ} (h : i' + 2 ≤ i) {x : Edge}
    (hx : x ∈ cellE (cellJ c s i)) : x ∉ cellE (cellJ c s i') := by
  obtain ⟨p, q⟩ := c
  cases s <;> simp [cellE, cellJ, bot, top, lft, rgt] at hx ⊢ <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega
end ULHC
