-- Prove2me | solution 1 for ULHC.front_corner_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:24.822648+00:00
-- url     : https://prove2.me/submissions/62b2a5ad-afc8-41de-a52c-75d8f35001e4

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) {i j : ℕ} (h : i ≠ j) :
    front1 (cellJ c s i) s ≠ front1 (cellJ c s j) s ∧ front1 (cellJ c s i) s ≠ front2 (cellJ c s j) s ∧
      front2 (cellJ c s i) s ≠ front1 (cellJ c s j) s ∧ front2 (cellJ c s i) s ≠ front2 (cellJ c s j) s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [front1, front2, cellJ] <;> omega
end ULHC
