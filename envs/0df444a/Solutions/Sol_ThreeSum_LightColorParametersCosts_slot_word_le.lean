-- Prove2me | solution 1 for ThreeSum.LightColorParametersCosts.slot_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:07.509585+00:00
-- url     : https://prove2.me/submissions/05759c73-c64a-46c1-9102-d16d377e5151

import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParametersCosts
open ColorParameters Scales StageBounds
namespace ThreeSum.LightColorParametersCosts
theorem _root_.solution {n t : ℕ} (ht : t < count (width n)) :
    t+width n+10 ≤ wordBudget n := by unfold wordBudget; omega
end ThreeSum.LightColorParametersCosts
