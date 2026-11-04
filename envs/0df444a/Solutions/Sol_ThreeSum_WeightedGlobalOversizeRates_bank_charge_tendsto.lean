-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.bank_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:12.804825+00:00
-- url     : https://prove2.me/submissions/fa8aa9fc-8d42-451c-b5f0-6681fac9abb9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_family_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_bank_charge_tendsto


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K : ℕ} (hK : 0 < K) :
    Tendsto (bankCharge K) atTop (𝓝 (2*bankEntropy/Hpi+8/K)) :=
  WeightedGlobalFiniteLedger.bank_charge_tendsto.add (family_charge_tendsto hK)
end ThreeSum.WeightedGlobalOversizeRates
