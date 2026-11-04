-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.mem_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:01.385763+00:00
-- url     : https://prove2.me/submissions/aabb2894-b1d9-482b-9428-e0229c2b1529

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ digitCost d ≤ t := by
  simp [digits]
end ThreeSum.WeightedEnumeration
