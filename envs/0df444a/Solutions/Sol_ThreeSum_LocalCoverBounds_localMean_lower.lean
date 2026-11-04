-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localMean_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:50.940123+00:00
-- url     : https://prove2.me/submissions/4b77a82c-b4ed-4f72-abff-be9e78f58ed8

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
import Definitions.Def_WeightedCache3SUM_Alias_e9faaede4c647b1a
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_upper

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (h : ℕ) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean (512 * h) h (localPrime h) :=
  mean_lower (by omega) (localPrime_pos h) (localPrime_sq_upper h)
end ThreeSum.LocalCoverBounds
