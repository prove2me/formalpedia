-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedCollisionRate.charge_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:02:12.533869+00:00
-- url     : https://prove2.me/submissions/506e0d21-bf1e-4139-8ef3-8be64cbc6538

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_limit_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedCollisionRate
theorem _root_.solution {K : ℕ} (hK : 0<K) :
    ∀ᶠ m : ℕ in atTop, charge K m<(7483/10000 : ℝ) :=
  (charge_tendsto hK).eventually (gt_mem_nhds (limit_lt hK))
end ThreeSum.WeightedGlobalPairedCollisionRate
