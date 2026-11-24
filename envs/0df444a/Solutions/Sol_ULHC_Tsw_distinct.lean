-- Prove2me | solution 1 for ULHC.Tsw_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:43.846427+00:00
-- url     : https://prove2.me/submissions/8b58d36b-6eed-48f0-af15-f7afede709f7

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
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
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (j : ℕ) :
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s j) s ∧ lat1 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧ lat1 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧
    lat1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧ lat2 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat2 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat1 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    outer1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s := by
  obtain ⟨a, b⟩ := c
  cases s <;> simp [lat1, lat2, outer1, outer2, cellJ, bot, top, lft, rgt] <;> omega
end ULHC
