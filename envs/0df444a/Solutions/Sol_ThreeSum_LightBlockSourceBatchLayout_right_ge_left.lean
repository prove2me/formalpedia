-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.right_ge_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:11.152463+00:00
-- url     : https://prove2.me/submissions/42816f12-ca93-49c6-8ead-e6907224b3f9

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i : ℕ) :
    leftBase base count W cut i ≤ rightBase base count W cut i := Nat.le_add_right _ _
end ThreeSum.LightBlockSourceBatchLayout
