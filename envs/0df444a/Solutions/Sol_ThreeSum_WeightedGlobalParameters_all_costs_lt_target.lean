-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.all_costs_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:01.906693+00:00
-- url     : https://prove2.me/submissions/a81b2785-4b43-46df-9c56-9ffc8a3fd9ad

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_all_costs_lt_certificate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_certificate_lt_target
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : ∀ t ∈ costLedger, t < targetExponent := by
  intro t ht
  exact lt_trans (all_costs_lt_certificate t ht) certificate_lt_target
end ThreeSum.WeightedGlobalParameters
