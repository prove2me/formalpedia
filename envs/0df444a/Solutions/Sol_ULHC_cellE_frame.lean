-- Prove2me | solution 1 for ULHC.cellE_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:08.798885+00:00
-- url     : https://prove2.me/submissions/eee96fe0-6543-4e2a-9f7a-c7d2f846d837

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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    cellE c = {back c s, front c s, lat1 c s, lat2 c s} := by
  cases s <;> ext e <;>
    simp only [cellE, back, front, lat1, lat2, sideEdge, Side.opp, Finset.mem_insert,
      Finset.mem_singleton] <;> tauto
end ULHC
