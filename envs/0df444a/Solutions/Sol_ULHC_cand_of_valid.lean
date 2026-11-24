-- Prove2me | solution 1 for ULHC.cand_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:08.268281+00:00
-- url     : https://prove2.me/submissions/3390258f-a7ac-482f-a848-1f28f9f26238

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_mem_allStrips


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {σ : StripSpec} (h : ValidStrip V G σ) : σ ∈ cand V G := by
  obtain ⟨h1, hp, hc, _⟩ := h
  exact Finset.mem_union_left _ (mem_allStrips.2 ⟨h1, hp, hc⟩)
end ULHC
