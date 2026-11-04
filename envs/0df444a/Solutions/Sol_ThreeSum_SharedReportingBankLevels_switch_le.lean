-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.switch_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:59:55.999203+00:00
-- url     : https://prove2.me/submissions/80c52d31-6995-43f8-b752-a1b101bf24c9

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_WeightedCache3SUM_Alias_4ca9f0cf2a6baf04
import Theorems.Thm_ThreeSum_LightSwitch_index_le_residual
import Theorems.Thm_ThreeSum_Switch_candidates_nonempty


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution {h J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) :
    switch h J k ≤ residual h J k :=
  LightSwitch.index_le_residual (candidates_nonempty hk)
end ThreeSum.SharedReportingBankLevels
