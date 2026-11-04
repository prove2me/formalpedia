-- Prove2me | solution 1 for ThreeSum.BandRawA.localA_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:09.280564+00:00
-- url     : https://prove2.me/submissions/f8cfb48b-2e29-45e1-99de-416454f542f5

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_at_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    localA n g rs k < bandLength n g (ownerRecord n g rs k).a := by
  have hh := at_bounds hk
  unfold localA bandLength
  omega
end ThreeSum.BandRawA
