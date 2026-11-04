-- Prove2me | solution 1 for ThreeSum.LightMaskMinimum.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:26.542036+00:00
-- url     : https://prove2.me/submissions/419cc7c3-b934-4d2a-8b94-3695b592bfe2

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskMinimum
theorem _root_.solution (L : ℕ) : time L ≤ 500*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith
end ThreeSum.LightMaskMinimum
