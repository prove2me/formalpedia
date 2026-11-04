-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.payload_le_finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:39:06.929086+00:00
-- url     : https://prove2.me/submissions/c4887116-db74-4fe3-a4e0-f2276ec66a2a

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _
end ThreeSum.SharedReportingBankHeader
