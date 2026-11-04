-- Prove2me | solution 1 for ThreeSum.LightRawAKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:09.121398+00:00
-- url     : https://prove2.me/submissions/39103c1d-1c61-4180-9005-c6dedc9b2a37

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightRawAKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRawAKeys
theorem _root_.solution (n U : ℕ) : time n U ≤ 220*(n+1)*(Nat.log 2 (U+1)+1) := by
  unfold time residuesTime residueBudget LightReportingAffine.time
  nlinarith
end ThreeSum.LightRawAKeys
