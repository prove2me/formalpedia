-- Prove2me | solution 1 for ULHC.cells_of_cand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:09.965081+00:00
-- url     : https://prove2.me/submissions/385bc942-cd83-4fab-94c8-ce75f8136e65

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_allStrips
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {σ : StripSpec} (h : σ ∈ cand V G) :
    1 ≤ σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  simp only [cand, Finset.mem_union, Finset.mem_biUnion] at h
  rcases h with h | ⟨_, _, h⟩
  · obtain ⟨h1, _, hc⟩ := mem_allStrips.1 h
    exact ⟨h1, hc⟩
  · obtain ⟨h1, _, hc⟩ := mem_allStrips.1 h
    exact ⟨h1, hc⟩
end ULHC
