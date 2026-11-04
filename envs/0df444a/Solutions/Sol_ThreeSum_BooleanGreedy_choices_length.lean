-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.choices_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:56.706029+00:00
-- url     : https://prove2.me/submissions/adaff0cb-cb55-4f01-b6ce-d3ad22198067

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_ThreeSum_Cover_greedyChoices_length


set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators
namespace ThreeSum.BooleanGreedy
theorem _root_.solution (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..
end ThreeSum.BooleanGreedy
