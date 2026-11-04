-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSeedData.collisionC_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:56:48.887851+00:00
-- url     : https://prove2.me/submissions/c34e7bc1-4867-4610-8790-c25532bebdfc

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_updated_hash
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_newC_eq
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_collision_count
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedData
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaSeedData
theorem _root_.solution (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i t, 0≤(p : ℤ)+R i t) :
    (data I A r b k ℓ seed row L R O rows catalog).collisionC=
      (TernaryOriginalCollisions.nextCollisions ℓ (fun i : Fin I.nC => fun t => (R i.val t : ZMod p))
        (fun i : Fin I.nC => hash row r R i.val) seed : ℤ) := by
  unfold Data.collisionC
  simp_rw [newC_eq I A r b k ℓ seed row L R O rows catalog hR,updated_hash]
  rw [TernaryOriginalAppendSemantics.collision_count]
  rfl
end ThreeSum.WeightedGlobalArenaSeedData
