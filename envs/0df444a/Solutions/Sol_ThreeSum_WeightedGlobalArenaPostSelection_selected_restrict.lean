-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPostSelection.selected_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:35:55.601581+00:00
-- url     : https://prove2.me/submissions/094eab14-f513-447d-92e6-70abdfda82e3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaPostSelection
theorem _root_.solution (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    selectedInput I U radix nA H A B C keysB keysC =
      WeightedGlobalArenaPairRestriction.restrict
        (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)
        (indices keysB I.nB).length (indices keysC I.nC).length
        (index keysB I.nB) (index keysC I.nC) := by
  rfl
end ThreeSum.WeightedGlobalArenaPostSelection
