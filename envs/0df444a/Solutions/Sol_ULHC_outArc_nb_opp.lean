-- Prove2me | solution 1 for ULHC.outArc_nb_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:18:11.332232+00:00
-- url     : https://prove2.me/submissions/27c7c09d-61be-44f0-91c9-9b1b6a0938e7

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
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
theorem _root_.solution (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F (nb c s) s.opp = !outArc F c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [outArc, nb, Side.opp, bot, top, lft, rgt]
end ULHC
