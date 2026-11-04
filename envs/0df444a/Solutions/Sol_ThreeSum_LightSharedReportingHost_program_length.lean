-- Prove2me | solution 1 for ThreeSum.LightSharedReportingHost.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:45:28.219852+00:00
-- url     : https://prove2.me/submissions/1bd666ac-2733-4f3d-88d4-c784250b38ac

import Definitions.Def_Submission_ThreeSum_LightSharedReportingBank
import Definitions.Def_Submission_ThreeSum_LightSharedReportingCounts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Definitions.Def_Submission_ThreeSum_SourceControlLayout
import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingHost
open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankRows
open SharedReportingBankHeader
set_option maxHeartbeats 3900000
set_option maxRecDepth 16000
namespace ThreeSum.LightSharedReportingHost
theorem _root_.solution : program.length=75 := rfl
end ThreeSum.LightSharedReportingHost
