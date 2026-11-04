-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.primeCandidates_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:21.659006+00:00
-- url     : https://prove2.me/submissions/dc60f124-447c-4cfe-b459-0c5e7b9251cd

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (N : ℕ) :
    (primeCandidates N).card ≤ 2 * rootCeiling N + 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
end ThreeSum.LocalCoverBounds
