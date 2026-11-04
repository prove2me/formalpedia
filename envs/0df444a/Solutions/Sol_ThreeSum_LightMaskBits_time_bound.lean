-- Prove2me | solution 1 for ThreeSum.LightMaskBits.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:24.014799+00:00
-- url     : https://prove2.me/submissions/f2589643-1422-4368-950b-e455b4c6c032

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskBits
theorem _root_.solution (L : ℕ) : time L ≤ 300*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith
end ThreeSum.LightMaskBits
