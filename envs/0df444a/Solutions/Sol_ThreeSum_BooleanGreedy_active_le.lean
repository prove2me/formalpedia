-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.active_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:24.538267+00:00
-- url     : https://prove2.me/submissions/6b79c0db-957a-45e7-8736-ce34ac564db5

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy

set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators
namespace ThreeSum.BooleanGreedy
theorem _root_.solution (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) :
    active matrix rows cols t j ≤ 1 := by unfold active; split <;> omega
end ThreeSum.BooleanGreedy
