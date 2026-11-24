-- Prove2me | solution 1 for ULHC.front1_not_corner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:19.350378+00:00
-- url     : https://prove2.me/submissions/1270007c-020a-4196-98f4-3c051a5e94ef

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
theorem _root_.solution (d : Pt) (s : Side) :
    front1 (nb d s) s ∉ ({back1 d s, back2 d s, front1 d s, front2 d s} : Finset Pt) := by
  obtain ⟨p, q⟩ := d
  cases s <;> simp [back1, back2, front1, front2, nb] <;> omega
end ULHC
