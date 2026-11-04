-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:52.133198+00:00
-- url     : https://prove2.me/submissions/1bb2fb71-a9a0-46f1-808b-c50cddf445cf

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
theorem _root_.solution (C J mu : ℕ) :
    time C J mu ≤ 1000*(J+mu+root C J+divisor mu+1) := by
  have he := Nat.div_le_self mu 20
  have hb := Nat.div_le_self (numerator C J mu) (divisor mu)
  have hn : numerator C J mu ≤ root C J+divisor mu := Nat.sub_le _ _
  have hs : Nat.sqrt (C^J-1) ≤ root C J := by unfold root rootCeiling; omega
  unfold time LightNatPower.time LightSmallDivide.time sqrtTime
  omega
end ThreeSum.LightGlobalSizes
