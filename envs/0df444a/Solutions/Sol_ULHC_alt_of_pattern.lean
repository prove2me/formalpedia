-- Prove2me | solution 1 for ULHC.alt_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:31:32.891262+00:00
-- url     : https://prove2.me/submissions/92acf77c-66ad-417e-96bd-fe799f227117

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} {tf : Side} (h1 : back d tf ∈ F) (h2 : front d tf ∈ F)
    (h3 : lat1 d tf ∉ F) (h4 : lat2 d tf ∉ F) : Alt F d := by
  unfold Alt
  cases tf <;> simp only [back, front, lat1, lat2, sideEdge, Side.opp] at h1 h2 h3 h4 <;> tauto
end ULHC
