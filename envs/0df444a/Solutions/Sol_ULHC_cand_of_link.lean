-- Prove2me | solution 1 for ULHC.cand_of_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:11.141045+00:00
-- url     : https://prove2.me/submissions/ca2e52c1-65c7-4d7c-8f8f-d41702b24f6b

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_endCell_isCell
import Theorems.Thm_ULHC_mem_allStrips


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {b c : StripSpec} (h1 : 1 ≤ b.n)
    (hb : ∀ j < b.n, IsCell V (cellJ b.c b.s j)) (hl : CR2 V G b c) : c ∈ cand V G := by
  obtain ⟨_, _, hc1, hp, hc, _⟩ := hl
  have hu := endCell_isCell h1 hb
  exact Finset.mem_union_right _ (Finset.mem_biUnion.2
    ⟨endCell b, Finset.mem_filter.2 ⟨hu.1, hu⟩, mem_allStrips.2 ⟨hc1, hp, hc⟩⟩)
end ULHC
