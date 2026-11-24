-- Prove2me | solution 1 for ULHC.length_cellList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:57.544676+00:00
-- url     : https://prove2.me/submissions/043007f6-8dd4-4828-84a0-029fbd381275

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (V : Finset Pt) : (cellList V).length ≤ V.card := by
  unfold cellList
  rw [List.length_map, Finset.length_sort, Finset.card_map]
  exact card_filter_le _ _
end ULHC
