-- Prove2me | solution 1 for ThreeSum.LightBandCandidates.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:27.487915+00:00
-- url     : https://prove2.me/submissions/a5b9823d-8dc5-4f71-ae95-64a5423bc396

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}
namespace ThreeSum.LightBandCandidates
theorem _root_.solution (a b c : ℕ) :
    time a b c ≤ 1000*(LightBandEnumeration.count a b c+a+b+c+1) := by
  unfold time LightBandCandidatesTable.time LightBandCandidatesRow.time
    LightBandCandidatesCell.time LightBandEnumeration.count
  nlinarith
end ThreeSum.LightBandCandidates
