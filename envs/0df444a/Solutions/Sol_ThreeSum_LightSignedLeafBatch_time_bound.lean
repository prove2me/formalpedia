-- Prove2me | solution 1 for ThreeSum.LightSignedLeafBatch.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:30.35778+00:00
-- url     : https://prove2.me/submissions/76bf7549-36ca-4902-a7fc-9fed1502ec26

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeafBatch
theorem _root_.solution (W n : ℕ) : time W n ≤ 9400*(W+1)^2*(n+1) := by
  have h := LightSignedLeafCell.time_bound W
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  have hsmall := Nat.mul_le_mul_left n (show 55 ≤ 100*(W+1)^2 by omega)
  unfold time
  nlinarith
end ThreeSum.LightSignedLeafBatch
