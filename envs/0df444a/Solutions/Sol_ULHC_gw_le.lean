-- Prove2me | solution 1 for ULHC.gw_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:10.859797+00:00
-- url     : https://prove2.me/submissions/e1d2479b-d2d2-4d7e-8714-6b6a16bb6fea

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_cells_of_cand
import Theorems.Thm_ULHC_mem_candN
import Theorems.Thm_ULHC_strip_len_le


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} {x : Node} (hx : x ∈ candN V G) : gw x ≤ V.card := by
  obtain ⟨_, hc⟩ := cells_of_cand (mem_candN.1 hx).1
  exact strip_len_le hc
end ULHC
