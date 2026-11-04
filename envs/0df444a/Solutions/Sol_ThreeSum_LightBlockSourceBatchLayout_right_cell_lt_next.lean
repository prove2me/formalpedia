-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.right_cell_lt_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:16.023805+00:00
-- url     : https://prove2.me/submissions/7ce15d9a-3b2d-4581-adab-90efc1c7a6aa

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_stage_cell_lt_end

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  rw [← right_end]
  exact stage_cell_lt_end hj hS
end ThreeSum.LightBlockSourceBatchLayout
