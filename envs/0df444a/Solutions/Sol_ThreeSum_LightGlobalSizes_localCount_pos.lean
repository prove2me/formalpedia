-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.localCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:34.114165+00:00
-- url     : https://prove2.me/submissions/a5523bfe-5dba-4d30-bbdd-b862e82ffab1

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
theorem _root_.solution (n : ℕ) : 0 < localCount n := Nat.choose_pos (by omega)
end ThreeSum.LightGlobalSizes
