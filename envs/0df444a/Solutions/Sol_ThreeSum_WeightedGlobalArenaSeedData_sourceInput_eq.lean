-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSeedData.sourceInput_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:02:41.738201+00:00
-- url     : https://prove2.me/submissions/0cae5699-866c-4c8c-a967-7bda744c63ad

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_newB_eq
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_newC_eq
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_newO_eq
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
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
    (hL : ∀ i t, 0≤(p : ℤ)+L i t) (hR : ∀ i t, 0≤(p : ℤ)+R i t) (hO : ∀ i t, 0≤(p : ℤ)+O i t) :
    sourceInput I A k (data I A r b k ℓ seed row L R O rows catalog)=
      WeightedGlobalArenaPrefixGroups.input I L R (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed))
        (root (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) O) (r+1) := by
  have hb := funext (newB_eq I A r b k ℓ seed row L R O rows catalog hL)
  have hc := funext (newC_eq I A r b k ℓ seed row L R O rows catalog hR)
  have ho := funext (newO_eq I A r b k ℓ seed row L R O rows catalog hO)
  unfold sourceInput Data.targets
  rw [hb,hc,ho]
  rfl
end ThreeSum.WeightedGlobalArenaSeedData
