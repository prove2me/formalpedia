-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixStep.retained_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:44:01.156638+00:00
-- url     : https://prove2.me/submissions/7eb0999e-423a-402a-98eb-51920104a85c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixStep_next_eq_physical
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_value_eq_model
import Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_retained_next_le
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPrefixStep
theorem _root_.solution (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (r K : ℕ)
    (hrow : row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    value maps τ cap I L R row root Q (r+1) K≤
      nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
        (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by
  rw [value_eq_model]
  exact ((M maps τ cap I L R row root).retained_next_le ℓ seed hrow).trans_eq
    (next_eq_physical maps τ cap I L R row root Q ℓ seed r K)
end ThreeSum.WeightedGlobalArenaPrefixStep
