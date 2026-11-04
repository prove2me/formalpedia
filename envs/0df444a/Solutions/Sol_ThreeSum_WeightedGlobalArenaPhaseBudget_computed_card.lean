-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPhaseBudget.computed_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:11:54.607321+00:00
-- url     : https://prove2.me/submissions/85a24f1f-ed6b-4d91-8376-bb455167c36c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Theorems.Thm_ThreeSum_WeightedGlobalComputedExtensionMenu_field_card


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPhaseBudget
theorem _root_.solution (M radix K n U c : ℕ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus p
      (LightWeightedGlobalDimensions.dim M radix p K n U) c))] :
    Fintype.card (AdjoinRoot (WeightedGlobalComputedExtensionMenu.modulus p
      (LightWeightedGlobalDimensions.dim M radix p K n U) c))=
      p^(menuDegree p (LightWeightedGlobalDimensions.J M radix n U+2) K) :=
  WeightedGlobalComputedExtensionMenu.field_card
end ThreeSum.WeightedGlobalArenaPhaseBudget
