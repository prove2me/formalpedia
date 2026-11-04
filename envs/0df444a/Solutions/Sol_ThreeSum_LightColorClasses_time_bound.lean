-- Prove2me | solution 1 for ThreeSum.LightColorClasses.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:48.647275+00:00
-- url     : https://prove2.me/submissions/1e643b2c-02d5-4cf2-8b12-8537c745b3e0

import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorClasses
open Light ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorClasses
theorem _root_.solution (W n : ℕ) : time W n ≤ 1200*(W+1)*(n+1) := by
  have h := LightColorArray.time_bound W n
  unfold time LightClassFilter.time
  nlinarith
end ThreeSum.LightColorClasses
