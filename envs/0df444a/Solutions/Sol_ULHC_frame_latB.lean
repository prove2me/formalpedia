-- Prove2me | solution 1 for ULHC.frame_latB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:32:15.587415+00:00
-- url     : https://prove2.me/submissions/ff337cd7-571f-4268-8bdc-a118e5f6998b

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
import Theorems.Thm_ULHC_opp_opp
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
theorem _root_.solution : front d (latB s) = lat2 d s ∧ back d (latB s) = lat1 d s ∧
    ((lat1 d (latB s) = back d s ∧ lat2 d (latB s) = front d s) ∨
      (lat1 d (latB s) = front d s ∧ lat2 d (latB s) = back d s)) := by
  refine ⟨(lat2_eq d s).symm, ?_, ?_⟩
  · show sideEdge d (latB s).opp = lat1 d s
    rw [lat1_eq, latB_eq_opp, opp_opp]
  · cases s <;> simp [lat1, lat2, back, front, latB, sideEdge, Side.opp]
end ULHC
