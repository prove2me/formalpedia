-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.bank_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:38.858365+00:00
-- url     : https://prove2.me/submissions/32e0cd64-4592-4cb7-b784-7ec73fbb9fed

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution :
    Tendsto bankCharge atTop (𝓝 (2*bankEntropy/Hpi)) :=
  tendsto_const_nhds.div actual_output_rate Hpi_pos.ne'
end ThreeSum.WeightedGlobalFiniteLedger
