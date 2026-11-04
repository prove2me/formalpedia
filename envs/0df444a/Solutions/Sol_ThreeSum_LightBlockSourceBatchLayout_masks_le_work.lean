-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.masks_le_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:03.70962+00:00
-- url     : https://prove2.me/submissions/25c3d7bc-1ece-4246-b0f9-ef8745fb0ee6

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut : ℕ) :
    maskBase base count W cut ≤ work base count W cut := by
  unfold work rowOut bitBase
  omega
end ThreeSum.LightBlockSourceBatchLayout
