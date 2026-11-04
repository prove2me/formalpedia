-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.banks_le_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:52.179036+00:00
-- url     : https://prove2.me/submissions/95505b34-d795-4974-a28e-d91a21237304

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_slot

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut : ℕ) : banks base count ≤ work base count W cut := by
  have hm := banks_le_slot base count W cut count
  unfold work rowOut bitBase maskBase
  omega
end ThreeSum.LightBlockSourceBatchLayout
