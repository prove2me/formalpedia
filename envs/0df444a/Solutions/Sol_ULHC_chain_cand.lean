-- Prove2me | solution 1 for ULHC.chain_cand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:13.076665+00:00
-- url     : https://prove2.me/submissions/89f1b504-3bfd-445e-b645-493852d921d9

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_link_cells
import Theorems.Thm_ULHC_cand_of_link
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
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution : ∀ (L : List StripSpec) (b : StripSpec), 1 ≤ b.n →
    (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → ∀ c ∈ L, c ∈ cand V G
  | [], _, _, _, _, c, hc => by simp at hc
  | τ :: L, b, h1, hb, hch, c, hc => by
    obtain ⟨_, hl, hrest⟩ := hch
    obtain ⟨hτ1, hτc⟩ := link_cells hl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact cand_of_link h1 hb hl
    · exact solution L τ hτ1 hτc hrest c hc
end ULHC
