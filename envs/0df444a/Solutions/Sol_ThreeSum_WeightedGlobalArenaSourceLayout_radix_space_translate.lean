-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceLayout.radix_space_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:05:13.245229+00:00
-- url     : https://prove2.me/submissions/235ab0a4-a98f-4243-8680-bd39712a7496

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost
namespace ThreeSum.WeightedGlobalArenaSourceLayout
theorem _root_.solution (dst m j : ℕ) :
    LightRadixKeys.space dst m j=dst+LightRadixKeys.space 0 m j := by
  unfold LightRadixKeys.space
  omega
end ThreeSum.WeightedGlobalArenaSourceLayout
