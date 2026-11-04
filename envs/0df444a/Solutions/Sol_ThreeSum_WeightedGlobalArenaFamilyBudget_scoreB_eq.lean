-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFamilyBudget.scoreB_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:04:32.761797+00:00
-- url     : https://prove2.me/submissions/0f921760-1784-484c-b888-a1a3b183c7ee

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_collisionB_eq
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
namespace ThreeSum.WeightedGlobalArenaFamilyBudget
theorem _root_.solution (i : ℕ) (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val) :
    (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreB i=
      (nextCollision A ℓ row L r I.nB (seedAt e i) : ℤ) :=
  collisionB_eq I A r b i ℓ (seedAt e i) row _ _ _ rows catalog hL
end ThreeSum.WeightedGlobalArenaFamilyBudget
