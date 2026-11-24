-- Prove2me | solution 1 for ULHC.rev_cellJ_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:18.682891+00:00
-- url     : https://prove2.me/submissions/cf01a25b-8a5a-4f2f-baf8-25e020f9c1f9

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (i m : ℕ) :
    cellJ (cellJ c s (i + m)) s.opp i = cellJ c s m := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellJ, Side.opp, Nat.cast_add] <;> ring_nf
end ULHC
