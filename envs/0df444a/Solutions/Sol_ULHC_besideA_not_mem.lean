-- Prove2me | solution 1 for ULHC.besideA_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:25.093802+00:00
-- url     : https://prove2.me/submissions/58dc3038-f1ba-4063-8d44-86bce74c8819

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
theorem _root_.solution (c : Pt) (s : Side) {m j i : ℕ} (hi : i < m) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s m) (latA s)) s j)) : x ∉ cellE (cellJ c s i) := by
  obtain ⟨p, q⟩ := c
  cases s <;> simp [cellE, nb, latA, cellJ, bot, top, lft, rgt] at hx ⊢ <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega
end ULHC
