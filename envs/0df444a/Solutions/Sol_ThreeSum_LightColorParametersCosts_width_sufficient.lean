-- Prove2me | solution 1 for ThreeSum.LightColorParametersCosts.width_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:04.923688+00:00
-- url     : https://prove2.me/submissions/6d8f8cf1-aa7b-4159-a87c-4440e98ca254

import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParametersCosts
open ColorParameters Scales StageBounds
namespace ThreeSum.LightColorParametersCosts
theorem _root_.solution (n : ℕ) : n ≤ 2^width n := Nat.lt_log2_self.le
end ThreeSum.LightColorParametersCosts
