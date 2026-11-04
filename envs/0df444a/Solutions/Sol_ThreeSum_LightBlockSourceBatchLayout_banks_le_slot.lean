-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.banks_le_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:46:17.378098+00:00
-- url     : https://prove2.me/submissions/2120b9c3-5005-4d1d-9341-9f32d18c56fb

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i : ℕ) : banks base count ≤ slot base count W cut i :=
  Nat.le_add_right _ _
end ThreeSum.LightBlockSourceBatchLayout
