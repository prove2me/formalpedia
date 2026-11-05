-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTensorBounds.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:55:59.726912+00:00
-- url     : https://prove2.me/submissions/1832cc9f-ffe5-4e27-ba99-fd05798b2dad

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTensorBounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTensorBounds
theorem _root_.solution {K J count count' V V' U U' : ℕ}
    (hc : count≤count') (hv : V≤V') (hu : U≤U') :
    WeightedGlobalTensorWordResources.word K J count V U≤
      WeightedGlobalTensorWordResources.word K J count' V' U' := by
  unfold WeightedGlobalTensorWordResources.word WeightedGlobalTensorWordResources.potentialWord
    WeightedGlobalTensorWordResources.polynomialBound
  gcongr
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTensorBounds
