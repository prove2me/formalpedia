-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFixedParameters.native_factor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:20:18.478388+00:00
-- url     : https://prove2.me/submissions/daad1f42-0061-4086-ae64-e0f40d94ad9f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_familyLength_pos
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_pairFactor_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaFixedParameters
theorem _root_.solution {K : ℕ} (hK : 0<K) (m : ℕ) : 0<9*pairFactor m (familyLength K m) K :=
  pairFactor_pos (familyLength_pos hK m)
end ThreeSum.WeightedGlobalArenaFixedParameters
