-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalArenaTemplate.fields_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:07:11.059693+00:00
-- url     : https://prove2.me/submissions/15521c48-115c-4f26-bc49-e859ea5ec5ad

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalArenaTemplate
theorem _root_.solution : ∀ f∈hostFields++seedFields, Good f := by decide
end ThreeSum.LightWeightedGlobalArenaTemplate
