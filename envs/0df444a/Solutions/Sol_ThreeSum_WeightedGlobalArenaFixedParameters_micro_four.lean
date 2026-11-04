-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFixedParameters.micro_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:06:24.736589+00:00
-- url     : https://prove2.me/submissions/8730bd63-8125-40ac-9140-ae8e2d64a2a7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaFixedParameters
theorem _root_.solution {K : ℕ} (hK : 0<K) : 4*microAllowance K<1 := by
  have hk : (1 : ℝ)≤K := by exact_mod_cast hK
  have hpos : (0 : ℝ)<K := by exact_mod_cast hK
  unfold microAllowance
  have hs : (1 : ℝ)≤(K : ℝ)^2 := by nlinarith
  have hd : (0 : ℝ)<100*(K : ℝ)^2 := by positivity
  rw [show (4 : ℝ)*(1/(100*(K : ℝ)^2))=4/(100*(K : ℝ)^2) by ring]
  apply (div_lt_iff₀ hd).mpr
  nlinarith
end ThreeSum.WeightedGlobalArenaFixedParameters
