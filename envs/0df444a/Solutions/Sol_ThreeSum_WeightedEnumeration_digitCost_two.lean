-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.digitCost_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:08.638381+00:00
-- url     : https://prove2.me/submissions/9316a111-a602-43b7-b91a-9987d18de631

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution : digitCost 2 = 1025 := by norm_num [digitCost]
end ThreeSum.WeightedEnumeration
