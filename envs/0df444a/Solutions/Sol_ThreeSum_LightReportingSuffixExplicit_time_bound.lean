-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixExplicit.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:42.617771+00:00
-- url     : https://prove2.me/submissions/5b575797-3d76-4b90-b9f9-00feb5cb1fa4

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixExplicit
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixExplicit
theorem _root_.solution {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 11000*(W+1)^3*(layerOffset c t+1) := by
  have hp : 1 ≤ (W+1)^2*(layerOffset c t+1) := Nat.mul_pos (by positivity) (by omega)
  have hm := Nat.mul_le_mul_right (roundTime W c t+30) ht
  unfold time roundTime at *
  nlinarith
end ThreeSum.LightReportingSuffixExplicit
