-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.band_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:02.465882+00:00
-- url     : https://prove2.me/submissions/9f7f2d9a-3b57-404c-a9df-703250e96e56

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes

set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalSizes
theorem _root_.solution (C J mu : ℕ) : band C J mu = root C J ⌈/⌉ divisor mu := rfl
end ThreeSum.LightGlobalSizes
