-- Prove2me | solution 1 for ULHC.node_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:48.360102+00:00
-- url     : https://prove2.me/submissions/1ec4b8d7-5a64-4add-bcfe-d64e248888a7

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_len_le_card
import Theorems.Thm_ULHC_cells_of_cand
import Theorems.Thm_ULHC_mem_candN


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (x : Node) (hx : x ∈ candN V G) : 1 ≤ x.σ.n ∧ x.σ.n ≤ V.card ∧
    ∀ j < x.σ.n, IsCell V (cellJ x.σ.c x.σ.s j) := by
  obtain ⟨h1, hc⟩ := cells_of_cand (mem_candN.1 hx).1
  exact ⟨h1, len_le_card hc, hc⟩
end ULHC
