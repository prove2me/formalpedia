-- Prove2me | solution 1 for ThreeSum.LightSubsetAddress.cell_offset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:45.85822+00:00
-- url     : https://prove2.me/submissions/100e7fe5-bc57-43db-bf81-8238b6f79c2b

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetAddress
theorem _root_.solution {W i j : ℕ} (hi : i ≤ W) (hj : j ≤ W) :
    i*(W+1)+j < tableSize W := by
  have hm := Nat.mul_le_mul_right (W+1) hi
  unfold tableSize
  nlinarith
end ThreeSum.LightSubsetAddress
