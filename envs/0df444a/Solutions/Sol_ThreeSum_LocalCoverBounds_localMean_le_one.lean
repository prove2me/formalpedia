-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localMean_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:57.332923+00:00
-- url     : https://prove2.me/submissions/fd70efa9-b8a1-4576-8772-b8d9a7755b5b

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_mean_le_one
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (h : ℕ) : mean (512 * h) h (localPrime h) ≤ 1 :=
  mean_le_one (localPrime_pos h) (localPrime_sq_lower h)
end ThreeSum.LocalCoverBounds
