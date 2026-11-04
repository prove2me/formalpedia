-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.selectedHash_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:11:54.350236+00:00
-- url     : https://prove2.me/submissions/12b7f2d1-2da2-4e8d-ae18-02a2ff1623a4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_featureMap_raw

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution (A : Inputs) (s : State (p := p) A) (r : ℕ) (raw : Coordinate A.J→ℤ) :
    selectedHash A s r (field raw)=hashMap A s r (fun i => (feature raw i.val : ZMod p)) := by
  exact congrArg (hashMap A s r) (featureMap_raw raw)
end ThreeSum.WeightedGlobalArenaSelectedSigned
