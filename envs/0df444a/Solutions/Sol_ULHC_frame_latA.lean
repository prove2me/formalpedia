-- Prove2me | solution 1 for ULHC.frame_latA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:32:15.082262+00:00
-- url     : https://prove2.me/submissions/c1f40471-27cf-4a9f-a357-9cdba5501014

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latB_eq_opp
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable (d : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : front d (latA s) = lat1 d s ∧ back d (latA s) = lat2 d s ∧
    ((lat1 d (latA s) = back d s ∧ lat2 d (latA s) = front d s) ∨
      (lat1 d (latA s) = front d s ∧ lat2 d (latA s) = back d s)) := by
  refine ⟨(lat1_eq d s).symm, ?_, ?_⟩
  · show sideEdge d (latA s).opp = lat2 d s
    rw [lat2_eq, latB_eq_opp]
  · cases s <;> simp [lat1, lat2, back, front, latA, sideEdge, Side.opp]
end ULHC
