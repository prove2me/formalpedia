-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.header_end_le_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:12.195215+00:00
-- url     : https://prove2.me/submissions/38c6c199-fa97-40ab-af54-b3aea5a0de68

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_slot

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i : ℕ} (hi : i < count) :
    base+2*i+2 ≤ slot base count W cut i := by
  have hb := banks_le_slot base count W cut i
  unfold banks at hb
  omega
end ThreeSum.LightBlockSourceBatchLayout
