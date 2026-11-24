-- Prove2me | solution 1 for ULHC.sideEdge_nb_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:18:00.510923+00:00
-- url     : https://prove2.me/submissions/cbcfcaa3-851e-46c0-ab85-f772c0b21dfd

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_back_nb
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : sideEdge (nb c s) s.opp = sideEdge c s := by
  have := back_nb c s; simpa [back, front] using this
end ULHC
