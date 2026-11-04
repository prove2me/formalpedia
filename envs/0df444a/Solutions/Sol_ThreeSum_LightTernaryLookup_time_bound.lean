-- Prove2me | solution 1 for ThreeSum.LightTernaryLookup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:27.6592+00:00
-- url     : https://prove2.me/submissions/43118497-86c5-4d83-9a90-cc26bd305969

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryLookup
theorem _root_.solution (L : ℕ) : time L ≤ 600 * (L+1) := by
  unfold time LightBandLookup.searchTime LightTernaryCell.time
  omega
end ThreeSum.LightTernaryLookup
