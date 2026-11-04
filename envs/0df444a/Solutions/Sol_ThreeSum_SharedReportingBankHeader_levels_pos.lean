-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.levels_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:48:24.117285+00:00
-- url     : https://prove2.me/submissions/534ca693-d008-4dab-bc2f-3745de5d2e39

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution (J : ℕ) : 0 < levels J := by unfold levels; omega
end ThreeSum.SharedReportingBankHeader
