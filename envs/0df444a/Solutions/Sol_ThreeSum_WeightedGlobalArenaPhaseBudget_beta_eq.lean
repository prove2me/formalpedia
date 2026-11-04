-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPhaseBudget.beta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:04:04.092463+00:00
-- url     : https://prove2.me/submissions/5969b273-99f6-47fc-8eca-90490e1716bd

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget

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
theorem _root_.solution (m F K : ℕ) :
    9*pairFactor m F K=9*F*(WeightedGlobalCoverScale.outputSize m)*(WeightedGlobalGoodOutputCatalog.Rbar m)^K := by
  unfold pairFactor WeightedGlobalCoverScale.outputSize WeightedGlobalGoodOutputCatalog.Rbar
  ring
end ThreeSum.WeightedGlobalArenaPhaseBudget
