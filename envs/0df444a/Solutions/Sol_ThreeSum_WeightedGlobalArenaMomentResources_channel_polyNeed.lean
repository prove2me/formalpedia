-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaMomentResources.channel_polyNeed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:44:40.969641+00:00
-- url     : https://prove2.me/submissions/4788f977-f32e-41f3-898b-1dea0ba27b98

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaMomentResources
theorem _root_.solution (maps : Fin F→Weight m p) (cap M H : ℕ) :
    PolyNeed (channelNeed maps cap M H) :=
  WeightedGlobalMomentChannelResources.polyNeed (envelope_powerBound maps cap M) (2*H)
end ThreeSum.WeightedGlobalArenaMomentResources
