-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.banks_le_left_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:17.182659+00:00
-- url     : https://prove2.me/submissions/600e4c25-fa78-46e6-ba20-688c2b68eb7f

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_slot
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_left_ge_slot

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    banks base count ≤ stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S := by
  have hs := (banks_le_slot base count W cut i).trans (left_ge_slot base count W cut i)
  unfold stageBase
  omega
end ThreeSum.LightBlockSourceBatchLayout
