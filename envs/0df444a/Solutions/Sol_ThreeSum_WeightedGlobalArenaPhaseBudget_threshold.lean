-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPhaseBudget.threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:34:46.873087+00:00
-- url     : https://prove2.me/submissions/03ae58b0-2af3-47fa-b6d5-1aa0a1a2410e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


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
theorem _root_.solution (m j K F U0 : ℕ) :
    U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)=
      scale m j K*(9*pairFactor m F K)^(j+1)*U0 := by
  have hs : (2^((fixedPi m 2)*K))^(j+1)=scale m j K := by
    unfold scale
    rw [←pow_mul]
    congr 1
    ring
  rw [mul_pow,hs]
  ring
end ThreeSum.WeightedGlobalArenaPhaseBudget
