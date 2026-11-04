-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.edgeCount_le_localPrime_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:55.194234+00:00
-- url     : https://prove2.me/submissions/6672d351-0e59-4522-81b9-765c91e71e2d

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_le_pow
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (h : ℕ) :
    outputCount (512 * h) h * groupSize h ≤ localPrime h ^ 2 :=
  (Nat.mul_le_mul_left _ (groupSize_le_pow h)).trans (localPrime_sq_lower h)
end ThreeSum.LocalCoverBounds
