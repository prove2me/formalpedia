-- Prove2me | solution 1 for ThreeSum.LightLocalCoverLayout.schedule_end_le_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:24.438702+00:00
-- url     : https://prove2.me/submissions/ac510c4e-edf6-4b14-9f18-a0af045df6e9

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
namespace ThreeSum.LightLocalCoverLayout
theorem _root_.solution (base h : ℕ) :
    scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ space base h := Nat.le_max_right ..
end ThreeSum.LightLocalCoverLayout
