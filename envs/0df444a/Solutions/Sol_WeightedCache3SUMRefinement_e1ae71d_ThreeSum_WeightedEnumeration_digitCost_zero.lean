-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:10.459652+00:00
-- url     : https://prove2.me/submissions/fc8495dd-8657-4308-8548-33794257e7a7

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
theorem _root_.solution : digitCost 0 = 0 := by norm_num [digitCost]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
