-- Prove2me | solution 1 for ULHC.back_side0_not_mem2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:31.021396+00:00
-- url     : https://prove2.me/submissions/c8ef2623-828e-4ee7-bcee-1ac6da4a2273

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
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
theorem _root_.solution (c : Pt) (s : Side) (i : ℕ) :
    back (nb c (latB s)) s ∉ cellE (cellJ c s i) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, back, nb, latB, cellJ, sideEdge, Side.opp, bot, top, lft, rgt]
end ULHC
