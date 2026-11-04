-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedStages.histogram_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:05.686645+00:00
-- url     : https://prove2.me/submissions/86ad643b-f13b-4675-a99c-73d2a0ec8ebd

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightHistogram_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
namespace ThreeSum.LightBlockSourceRetainedStages
theorem _root_.solution (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) :
    histogram p m shift v N r ≤ N := LightHistogram.count_le ..
end ThreeSum.LightBlockSourceRetainedStages
