-- Prove2me | solution 1 for ThreeSum.LightSharedReportingBank.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:30:51.136661+00:00
-- url     : https://prove2.me/submissions/4a84711e-950a-4a66-966b-d734589f0c49

import Definitions.Def_Submission_ThreeSum_LightSharedReportingPair
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSharedReportingBank

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingBank
open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankRows
set_option maxHeartbeats 3800000
set_option maxRecDepth 16000
namespace ThreeSum.LightSharedReportingBank
theorem _root_.solution : program.length=67 := rfl
end ThreeSum.LightSharedReportingBank
