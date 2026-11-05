-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:11.428669+00:00
-- url     : https://prove2.me/submissions/852c79f6-50a9-4909-b766-fb702f904721

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
theorem _root_.solution : digitCost 1 = 1369 := by norm_num [digitCost]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
