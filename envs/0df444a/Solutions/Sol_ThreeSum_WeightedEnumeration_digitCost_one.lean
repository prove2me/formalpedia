-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.digitCost_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:07.675103+00:00
-- url     : https://prove2.me/submissions/6697748d-fb91-402d-84bc-718b9d126813

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution : digitCost 1 = 512 := by norm_num [digitCost]
end ThreeSum.WeightedEnumeration
