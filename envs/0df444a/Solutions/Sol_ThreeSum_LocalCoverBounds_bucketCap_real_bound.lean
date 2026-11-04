-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.bucketCap_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:53.304183+00:00
-- url     : https://prove2.me/submissions/5c06a61f-56e9-450f-bb1a-47b913f7ba6f

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_mul_lt

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {V p : ℕ} (hp : 0 < p) :
    (bucketCap V p : ℝ) < 5 + 4 * (V : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (bucketCap V p : ℝ) * p < 4 * (p + (V : ℝ)) + p := by
    exact_mod_cast bucketCap_mul_lt (V := V) hp
  rw [show 5 + 4 * (V : ℝ) / p = (5 * p + 4 * V) / p by field_simp,
    lt_div_iff₀ hp0]
  nlinarith
end ThreeSum.LocalCoverBounds
