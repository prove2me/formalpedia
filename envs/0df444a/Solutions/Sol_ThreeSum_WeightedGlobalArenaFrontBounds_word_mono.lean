-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFrontBounds.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:05:47.506549+00:00
-- url     : https://prove2.me/submissions/9ddc12fa-e185-47fd-8b92-7b7ce15cf8c8

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaFrontBounds
theorem _root_.solution {N nb nb' G count count' R R' V V' : ℕ}
    (hb : nb≤nb') (hc : count≤count') (hr : R≤R') (hv : V≤V') :
    WeightedGlobalFrontendResources.word N nb G count R V≤
      WeightedGlobalFrontendResources.word N nb' G count' R' V' := by
  unfold WeightedGlobalFrontendResources.word WeightedGlobalFrontendResources.eulerBound
    WeightedGlobalFrontendResources.sourceZeta
  gcongr
end ThreeSum.WeightedGlobalArenaFrontBounds
