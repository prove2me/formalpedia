-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceBounds.local_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:05:46.104596+00:00
-- url     : https://prove2.me/submissions/8f78995c-4a27-4046-b54f-0b7598b02d28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceBounds
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :
    (localRecords maps cap right).length≤sourceWidth maps cap := by
  cases right <;> unfold sourceWidth <;> omega
end ThreeSum.WeightedGlobalArenaSourceBounds
