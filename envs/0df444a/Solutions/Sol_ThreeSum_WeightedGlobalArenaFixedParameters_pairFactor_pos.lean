-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFixedParameters.pairFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:13:41.913571+00:00
-- url     : https://prove2.me/submissions/6ec61edb-1e2c-4186-8580-a0b6d1e2f2cf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaFixedParameters
theorem _root_.solution {K m F : ℕ} (hF : 0<F) : 0<9*pairFactor m F K := by
  have hM := outputSize_pos m
  unfold pairFactor
  change 0<9*(F*outputSize m*(2^(fixedPi m 1)*3^(fixedPi m 2))^K)
  positivity
end ThreeSum.WeightedGlobalArenaFixedParameters
