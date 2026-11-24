-- Prove2me | solution 1 for ULHC.front_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:23:54.535941+00:00
-- url     : https://prove2.me/submissions/0b19d831-06c0-457e-b2a1-6ff6fdc5ed36

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_par_cellJ
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_outArc_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {F : Finset Edge} {c : Pt} {s : Side} {o : Bool}
namespace ULHC
theorem _root_.solution (hp : ParOK c s o) (j : ℕ)
    (hf : front (cellJ c s j) s ∈ F ↔ j % 2 = 1) : outArc F (cellJ c s j) s = o := by
  rw [outArc_eq, par_cellJ, hp]
  have : decide (sideEdge (cellJ c s j) s ∈ F) = decide (j % 2 = 1) := by
    simp only [front] at hf; simp [hf]
  rw [this]
  cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one j with h | h <;>
    simp [h]
end ULHC
