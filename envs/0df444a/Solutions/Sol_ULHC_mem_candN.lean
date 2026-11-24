-- Prove2me | solution 1 for ULHC.mem_candN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:29.614811+00:00
-- url     : https://prove2.me/submissions/949d6f54-e9d3-4ae1-9772-3954bcd96b63

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
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
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {x : Node} :
    x ∈ candN V G ↔ x.σ ∈ cand V G ∧ x.pos ∈ ({1, 2, 3} : Finset ℕ) := by
  obtain ⟨σ, p⟩ := x
  simp only [candN, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨τ, hτ, q, hq, he⟩
    cases he
    exact ⟨hτ, hq⟩
  · rintro ⟨hσ, hp⟩
    exact ⟨σ, hσ, p, hp, rfl⟩
end ULHC
