-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPreparedOriginals.base_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:06:06.179968+00:00
-- url     : https://prove2.me/submissions/872d756c-5da8-48ed-a3d3-e8aa4bd6e4eb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalPreparedOriginals
theorem _root_.solution (free n U J C0 weightCap queryTime : ℕ) (A B C : List ℤ) :
    WeightedGlobalArenaSelectedSigned.base (input free n U J C0 weightCap queryTime A B C) J A.length=
      input free n U J C0 weightCap queryTime A B C := rfl
end ThreeSum.WeightedGlobalPreparedOriginals
