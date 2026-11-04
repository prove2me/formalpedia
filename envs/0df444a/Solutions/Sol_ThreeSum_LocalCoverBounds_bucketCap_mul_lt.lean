-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.bucketCap_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:33.624625+00:00
-- url     : https://prove2.me/submissions/4a7a9fb0-7ffd-4ec3-b186-8d46ae257706

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_formula

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {V p : ℕ} (hp : 0 < p) :
    bucketCap V p * p < 4 * (p + V) + p := by
  rw [bucketCap_formula]
  have hdiv := Nat.div_mul_le_self (4 * (p + V) + p - 1) p
  omega
end ThreeSum.LocalCoverBounds
