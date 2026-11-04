-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.left_cell_lt_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:04.774537+00:00
-- url     : https://prove2.me/submissions/e14ebef3-f85e-4ff1-80db-de44cc152c60

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_mono
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_left_cell_lt_next

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut k :=
  (left_cell_lt_next hj hS).trans_le (slot_mono base count W cut (by omega))
end ThreeSum.LightBlockSourceBatchLayout
