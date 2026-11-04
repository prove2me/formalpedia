-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.selectedPrime_sq_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:29.339168+00:00
-- url     : https://prove2.me/submissions/4946a261-67d8-42ed-827b-1d9acff444c7

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_le_rootCeiling_sq
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (N : ℕ) : N ≤ selectedPrime N ^ 2 := by
  exact (le_rootCeiling_sq N).trans
    (Nat.pow_le_pow_left (selectedPrime_spec N).2.1.le 2)
end ThreeSum.LocalCoverBounds
