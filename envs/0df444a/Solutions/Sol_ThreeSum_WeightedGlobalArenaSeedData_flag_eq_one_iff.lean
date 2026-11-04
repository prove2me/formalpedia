-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSeedData.flag_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:20:56.462861+00:00
-- url     : https://prove2.me/submissions/359292a0-6b2f-40f2-b246-33ee959fa0ee

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_flag_menu_iff
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff



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
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).flag=1 ↔
      seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows) :=
by
  change ((LightStoredSpan.admissibleFlag (rows.map (TernaryPhysicalDigitSpan.reversal A.J))
    (TernaryPhysicalDigitSpan.physicalDigits (seedRow (A.J+2) ℓ seed)) : ℕ) : ℤ)=1 ↔ _
  rw [Nat.cast_eq_one]
  exact TernaryPhysicalDigitSpan.flag_menu_iff ℓ rows seed
end ThreeSum.WeightedGlobalArenaSeedData
