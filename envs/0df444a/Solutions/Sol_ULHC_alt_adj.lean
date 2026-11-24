-- Prove2me | solution 1 for ULHC.alt_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:57.128622+00:00
-- url     : https://prove2.me/submissions/8212b5a3-caad-4e15-a693-e161e65b28ae

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
theorem _root_.solution {F : Finset Edge} {d : Pt} (ha : Alt F d) (tf : Side) :
    (sideEdge d tf ∈ F ↔ sideEdge d (latA tf) ∉ F) ∧ (sideEdge d tf ∈ F ↔ sideEdge d (latB tf) ∉ F) := by
  unfold Alt at ha
  cases tf <;> simp only [sideEdge, latA, latB] <;> tauto
end ULHC
