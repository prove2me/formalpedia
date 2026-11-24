-- Prove2me | solution 1 for ULHC.corner_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:45.510808+00:00
-- url     : https://prove2.me/submissions/13570aca-0584-44f2-af77-098814e6a100

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
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
theorem _root_.solution {m : ℕ} (h : m ≠ 0) :
    back1 c s ≠ front1 (cellJ c s m) s ∧ back1 c s ≠ front2 (cellJ c s m) s ∧
      front1 c s ≠ front1 (cellJ c s m) s ∧ front1 c s ≠ front2 (cellJ c s m) s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, front1, front2, cellJ] <;> omega
end ULHC
