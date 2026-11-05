-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:33:23.29426+00:00
-- url     : https://prove2.me/submissions/ba837fce-d8b8-45fa-a01a-a6dd1d4bd1f0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds
theorem _root_.solution {N nb nb' G count count' R R' V V' : ℕ}
    (hb : nb≤nb') (hc : count≤count') (hr : R≤R') (hv : V≤V') :
    WeightedGlobalFrontendResources.word N nb G count R V≤
      WeightedGlobalFrontendResources.word N nb' G count' R' V' := by
  unfold WeightedGlobalFrontendResources.word WeightedGlobalFrontendResources.eulerBound
    WeightedGlobalFrontendResources.sourceZeta
  gcongr
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds
