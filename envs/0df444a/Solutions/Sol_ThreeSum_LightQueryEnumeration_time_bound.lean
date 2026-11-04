-- Prove2me | solution 1 for ThreeSum.LightQueryEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:19.401848+00:00
-- url     : https://prove2.me/submissions/b39e7082-ae2a-4ffb-8c3b-cdbea0088c32

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryEnumeration
theorem _root_.solution {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := LightQueryWeights.time_bound W
  have he := LightSubsetEnumeration.time_bound c t
  unfold time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]
end ThreeSum.LightQueryEnumeration
