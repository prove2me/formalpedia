-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.right_cell_lt_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:47.640321+00:00
-- url     : https://prove2.me/submissions/c1789761-3957-4083-ac06-cb9ab487db51

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_mono
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_cell_lt_next

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut k :=
  (right_cell_lt_next hj hS).trans_le (slot_mono base count W cut (by omega))
end ThreeSum.LightBlockSourceBatchLayout
