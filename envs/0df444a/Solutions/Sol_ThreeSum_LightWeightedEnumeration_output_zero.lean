-- Prove2me | solution 1 for ThreeSum.LightWeightedEnumeration.output_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:46:36.469926+00:00
-- url     : https://prove2.me/submissions/0b0a77a7-b097-488f-8d8c-2d30dbe50967

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedEnumeration
theorem _root_.solution (weights : ℕ → ℕ) (L pref : ℕ) :
    output weights L 0 pref = [pref] := by
  cases L <;> rfl
end ThreeSum.LightWeightedEnumeration
