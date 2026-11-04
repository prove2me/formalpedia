-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.Hpi_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:25.067302+00:00
-- url     : https://prove2.me/submissions/28216e8b-adca-417d-9d28-f32d55045c45

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_Hn_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 0<Hpi := div_pos WeightedCacheParameters.Hn_pos log_two_pos
end ThreeSum.WeightedGlobalParameters
