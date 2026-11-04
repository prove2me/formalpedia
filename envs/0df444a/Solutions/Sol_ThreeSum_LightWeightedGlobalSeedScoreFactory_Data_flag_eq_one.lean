-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedScoreFactory.Data.flag_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:23:47.889448+00:00
-- url     : https://prove2.me/submissions/1001e761-6cbf-4e09-80c8-ba76e664e893

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_physical_span_iff


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
open scoped BigOperators
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
namespace Data
theorem _root_.solution {C : Config} [Fact C.p.Prime] (D : Data C) :
    D.flag=1 ↔ D.logicalRow∉TernaryPhysicalDigitSpan.forbidden D.logicalRows := by
  unfold flag
  rw [Nat.cast_eq_one,LightStoredSpan.admissibleFlag_eq_one]
  exact not_congr (TernaryPhysicalDigitSpan.physical_span_iff D.logicalRows D.logicalRow)
end Data
end ThreeSum.LightWeightedGlobalSeedScoreFactory
