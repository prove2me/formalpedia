-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.state_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:16.368159+00:00
-- url     : https://prove2.me/submissions/72fa4ddf-a04b-437d-baf0-e4683232c206

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_ThreeSum_Cover_greedyState_subset


set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators
namespace ThreeSum.BooleanGreedy
theorem _root_.solution (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    state matrix rows cols t ⊆ range cols := Cover.greedyState_subset ..
end ThreeSum.BooleanGreedy
