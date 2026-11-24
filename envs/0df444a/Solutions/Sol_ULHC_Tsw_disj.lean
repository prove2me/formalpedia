-- Prove2me | solution 1 for ULHC.Tsw_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:26.55212+00:00
-- url     : https://prove2.me/submissions/4d52fa4b-2eb0-4b77-ad4d-ec79ce1d105b

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
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
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution {j j' : ℕ} (hj : j % 2 = 1) (hj' : j' % 2 = 1) (h : j ≠ j') :
    Disjoint (Tsw c s j) (Tsw c s j') := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨a, b⟩ := c
  cases s <;>
    simp only [Tsw, Finset.mem_insert, Finset.mem_singleton, lat1, lat2, outer1, outer2, cellJ,
      bot, top, lft, rgt] at h1 h2 <;>
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, false_and, or_false,
      false_or] at h2 <;> omega
end ULHC
