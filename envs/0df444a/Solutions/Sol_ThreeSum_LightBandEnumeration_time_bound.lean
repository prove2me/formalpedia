-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:38:29.40072+00:00
-- url     : https://prove2.me/submissions/d1fb0ed1-c4d7-4a61-88fd-214859fee086

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
theorem _root_.solution (nA nB nC : ℕ) :
    time nA nB nC ≤ 1000*(count nA nB nC+nA+nB+nC+1)*(width nA nB nC+1) := by
  have heq : time nA nB nC = count nA nB nC*(120*width nA nB nC+190)+
      76*(nB+2*nA)+29*width nA nB nC+553 := by
    unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
      LightBandLookup.time LightBandLookup.searchTime count width
    ring
  rw [heq]
  generalize count nA nB nC = D
  generalize width nA nB nC = W
  nlinarith [Nat.zero_le (D*W),Nat.zero_le (nA*W),Nat.zero_le (nB*W),Nat.zero_le (nC*W)]
end ThreeSum.LightBandEnumeration
