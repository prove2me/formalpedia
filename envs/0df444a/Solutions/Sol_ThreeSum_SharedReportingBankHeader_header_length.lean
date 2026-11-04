-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.header_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:57:28.331782+00:00
-- url     : https://prove2.me/submissions/7f89d5bd-f80c-4ed9-b367-9b7bd4a10465

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution (free h J NB NC g : ℕ) : (header free h J NB NC g).length=9 := rfl
end ThreeSum.SharedReportingBankHeader
