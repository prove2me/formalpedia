-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.family_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:12:12.905206+00:00
-- url     : https://prove2.me/submissions/7cfacee7-bc39-49bc-a592-34ecf8abb40c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_inflation_rate_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K : ℕ} (hK : 0 < K) :
    Tendsto (familyCharge K) atTop (𝓝 (8/(K : ℝ))) := by
  have h := ((inflation_rate_tendsto hK).const_mul 8).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · field_simp [Hpi_pos.ne']
end ThreeSum.WeightedGlobalOversizeRates
