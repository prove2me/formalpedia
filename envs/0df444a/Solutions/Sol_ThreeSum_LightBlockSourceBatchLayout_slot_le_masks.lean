-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.slot_le_masks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:01.256742+00:00
-- url     : https://prove2.me/submissions/e0875cec-e942-4e64-825a-2c7b41ba8e6f

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_mono

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i : ℕ} (hi : i ≤ count) :
    slot base count W cut i ≤ maskBase base count W cut := slot_mono base count W cut hi
end ThreeSum.LightBlockSourceBatchLayout
