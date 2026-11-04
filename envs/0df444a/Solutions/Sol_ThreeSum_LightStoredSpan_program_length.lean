-- Prove2me | solution 1 for ThreeSum.LightStoredSpan.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:14.337102+00:00
-- url     : https://prove2.me/submissions/23080114-08ad-4236-8665-7379b6fea06f

import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightStoredSpan

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightStoredSpan
open Light ThreeSum.TernaryStoredSpan
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
attribute [local instance] Classical.propDecidable
variable {lim : Limits} {P : Program} {p J : ℕ} [Fact p.Prime]
namespace ThreeSum.LightStoredSpan
theorem _root_.solution : program.length=8 := rfl
end ThreeSum.LightStoredSpan
