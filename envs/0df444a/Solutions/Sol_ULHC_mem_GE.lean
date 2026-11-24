-- Prove2me | solution 1 for ULHC.mem_GE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:37.804852+00:00
-- url     : https://prove2.me/submissions/53420339-9232-49df-b09a-ff1ba31409f9

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
theorem _root_.solution {V : Finset Pt} {e : Edge} : e ∈ GE V ↔ IsEdge V e := by
  unfold GE
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_biUnion.2 ⟨e.p, h.1, ?_⟩, h⟩
    obtain ⟨d, p⟩ := e
    cases d <;> simp [eR, eU]
end ULHC
