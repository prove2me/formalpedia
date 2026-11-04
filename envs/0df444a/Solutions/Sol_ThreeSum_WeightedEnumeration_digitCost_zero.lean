-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.digitCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:24:55.750217+00:00
-- url     : https://prove2.me/submissions/064bf3ef-e01e-4ec6-9267-0a05ea6b04b3

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution : digitCost 0 = 0 := by norm_num [digitCost]
end ThreeSum.WeightedEnumeration
