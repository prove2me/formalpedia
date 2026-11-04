-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.banks_le_right_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:18.3112+00:00
-- url     : https://prove2.me/submissions/5a1bb7f8-0d7c-4624-97fa-1a834a7f655b

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_left_ge_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_ge_left

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    banks base count ≤ stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S := by
  have hs := ((banks_le_slot base count W cut i).trans
    (left_ge_slot base count W cut i)).trans (right_ge_left base count W cut i)
  unfold stageBase
  omega
end ThreeSum.LightBlockSourceBatchLayout
