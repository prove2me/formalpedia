-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaTensorBounds.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:19:26.427307+00:00
-- url     : https://prove2.me/submissions/b4f74616-fd8a-4506-ac3f-aace966bc183

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaTensorBounds
theorem _root_.solution {K J count count' V V' U U' : ℕ}
    (hc : count≤count') (hv : V≤V') (hu : U≤U') :
    WeightedGlobalTensorWordResources.word K J count V U≤
      WeightedGlobalTensorWordResources.word K J count' V' U' := by
  unfold WeightedGlobalTensorWordResources.word WeightedGlobalTensorWordResources.potentialWord
    WeightedGlobalTensorWordResources.polynomialBound
  gcongr
end ThreeSum.WeightedGlobalArenaTensorBounds
