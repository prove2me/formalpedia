-- Prove2me | solution 1 for ThreeSum.LightZetaCell.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:11.236278+00:00
-- url     : https://prove2.me/submissions/66cfd7c3-4fc5-40b6-a141-f4ab674013fa

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaCell
theorem _root_.solution (L : ℕ) : time L ≤ 2000*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightMaskErase.time LightSubsetOffset.time rankTime
  nlinarith
end ThreeSum.LightZetaCell
