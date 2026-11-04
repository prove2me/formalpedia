-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:22:17.815085+00:00
-- url     : https://prove2.me/submissions/b32f22b2-220d-4ee0-b993-61957b8b1f44

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCompleteFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceSetup
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open TernaryCanonicalDictionaries LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceSetup
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) :
    (setup (r := r) maps τ cap Q I).left.input=I.leftInput := rfl
end ThreeSum.WeightedGlobalArenaSourceSetup
