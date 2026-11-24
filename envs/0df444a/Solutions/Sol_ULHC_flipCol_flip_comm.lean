-- Prove2me | solution 1 for ULHC.flipCol_flip_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:03.096498+00:00
-- url     : https://prove2.me/submissions/12b9f230-cb1e-449a-96b5-4c37b0185448

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_flip_flip_comm
import Theorems.Thm_ULHC_APair_flip
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
theorem _root_.solution (G : Finset Edge) (c : Pt) (s : Side) (u : Pt) :
    ∀ n, flip (flipCol G c s n) u = flipCol (flip G u) c s n := by
  intro n
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    simp only [flipCol]
    rw [ih, flip_flip_comm]
end ULHC
