-- Prove2me | solution 1 for ULHC.sidesIn_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:35.105048+00:00
-- url     : https://prove2.me/submissions/c622dd87-3d7e-407d-8acf-777c0cba094e

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
namespace ULHC
theorem _root_.solution (B : Finset Edge) (d : Pt) (s : Side) :
    sidesIn B d = ind B (back d s) + ind B (front d s) + ind B (lat1 d s) + ind B (lat2 d s) := by
  cases s <;> simp only [sidesIn, back, front, lat1, lat2, sideEdge, Side.opp] <;> ring
end ULHC
