-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.left_cell_lt_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:14.907343+00:00
-- url     : https://prove2.me/submissions/3fc87428-e6e1-4b2f-bac6-048956d6c89a

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
    stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  have hs := stage_cell_lt_end (base := leftBase base count W cut i) hj hS
  have he := right_end base count W cut i
  unfold rightBase at he
  omega
end ThreeSum.LightBlockSourceBatchLayout
