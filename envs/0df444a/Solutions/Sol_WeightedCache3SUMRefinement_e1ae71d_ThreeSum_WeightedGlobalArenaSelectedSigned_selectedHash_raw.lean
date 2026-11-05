-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned.selectedHash_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:48:47.126606+00:00
-- url     : https://prove2.me/submissions/9970a704-e8df-4e96-a074-f0be8f55303e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_featureMap_raw

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution (A : Inputs) (s : State (p := p) A) (r : ℕ) (raw : Coordinate A.J→ℤ) :
    selectedHash A s r (field raw)=hashMap A s r (fun i => (feature raw i.val : ZMod p)) := by
  exact congrArg (hashMap A s r) (featureMap_raw raw)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
