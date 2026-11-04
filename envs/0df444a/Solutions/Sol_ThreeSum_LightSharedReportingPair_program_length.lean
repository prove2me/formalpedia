-- Prove2me | solution 1 for ThreeSum.LightSharedReportingPair.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:15:43.333516+00:00
-- url     : https://prove2.me/submissions/432c605a-5989-4ff6-9401-230a458dc798

import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_LightSharedReportingPair

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingPair
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankLayout SharedReportingBankLevels SharedReportingBankSources
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
namespace ThreeSum.LightSharedReportingPair
theorem _root_.solution : program.length=66 := rfl
end ThreeSum.LightSharedReportingPair
