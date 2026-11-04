-- Prove2me | solution 1 for ThreeSum.LightDownsetSize.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:12.346124+00:00
-- url     : https://prove2.me/submissions/9ca4d36d-d6c9-4797-8625-c453a656d199

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetSize
theorem _root_.solution (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith
end ThreeSum.LightDownsetSize
