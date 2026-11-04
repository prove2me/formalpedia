-- Prove2me | solution 1 for ThreeSum.LightZetaBatch.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:17.758404+00:00
-- url     : https://prove2.me/submissions/e6fc6d3f-75c7-455a-8abb-d64d8a6ef1ed

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaBatch
theorem _root_.solution (L n : ℕ) : time L n ≤ 2100*(L+1)^2*(n+1) := by
  have h := LightZetaCell.time_bound L
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  have hsmall := Nat.mul_le_mul_left n (show 40 ≤ 100*(L+1)^2 by omega)
  unfold time
  nlinarith
end ThreeSum.LightZetaBatch
