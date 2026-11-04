-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionScore.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:38.101444+00:00
-- url     : https://prove2.me/submissions/604c0d02-5ba9-4f7a-b7db-382bbe7d1430

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionScore
open Light Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalCollisionScore
theorem _root_.solution (n q : ℕ) : time n q=74*n+13*q+217 := by
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime sumTime
  ring
end ThreeSum.LightOriginalCollisionScore
