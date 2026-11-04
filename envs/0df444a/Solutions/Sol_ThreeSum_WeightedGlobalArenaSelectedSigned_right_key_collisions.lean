-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.right_key_collisions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:38:39.940531+00:00
-- url     : https://prove2.me/submissions/a269a729-e22d-4416-a7bc-94cad0741d46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_selectedHash_raw
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_key_collisions
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution (A : Inputs) (s : State (p := p) A) (r q U radix : ℕ) (C : ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (sourceRight (selectedHash A s r) U radix (C i.val)))).card=
      collisions A s.row (right U radix A.J C) r q := by
  simp_rw [sourceRight,selectedHash_raw]
  exact key_collisions A s r q (right U radix A.J C)
end ThreeSum.WeightedGlobalArenaSelectedSigned
