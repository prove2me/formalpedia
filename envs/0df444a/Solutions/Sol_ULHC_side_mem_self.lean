-- Prove2me | solution 1 for ULHC.side_mem_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:14.139173+00:00
-- url     : https://prove2.me/submissions/867ef8c5-42f8-4327-848a-0d55602abbc5

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
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
theorem _root_.solution (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE c := by
  cases tf <;> simp [cellE, sideEdge]
end ULHC
