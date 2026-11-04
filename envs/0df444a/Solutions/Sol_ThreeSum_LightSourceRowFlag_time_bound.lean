-- Prove2me | solution 1 for ThreeSum.LightSourceRowFlag.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:49.198459+00:00
-- url     : https://prove2.me/submissions/724821b3-4cfa-4263-84f3-f888d61a10ae

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceRowFlag
theorem _root_.solution (L U : ℕ) :
    time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold time LightSourceRowScan.time LightResidues.residueBudget LightSourceFlagTest.time
  nlinarith
end ThreeSum.LightSourceRowFlag
