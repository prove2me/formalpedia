-- Prove2me | solution 1 for ULHC.frame_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:35.723135+00:00
-- url     : https://prove2.me/submissions/9583c834-2298-4528-befe-ae8ff7985b27

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
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
theorem _root_.solution (d : Pt) (tf : Side) : back d tf ≠ lat1 d tf ∧ back d tf ≠ lat2 d tf ∧
    front d tf ≠ lat1 d tf ∧ front d tf ≠ lat2 d tf ∧ lat1 d tf ≠ lat2 d tf ∧ back d tf ≠ front d tf := by
  obtain ⟨p, q⟩ := d
  cases tf <;> simp [back, front, lat1, lat2, sideEdge, Side.opp, bot, top, lft, rgt]
end ULHC
