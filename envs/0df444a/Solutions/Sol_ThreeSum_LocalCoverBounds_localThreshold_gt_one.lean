-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.localThreshold_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:07.89243+00:00
-- url     : https://prove2.me/submissions/d793ac16-fd76-4c2c-ba27-a9d41c394030

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_concrete_output_gt_pow

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {h : ℕ} (hh : 0 < h) : 1 < localThreshold h := by
  have hm := concrete_output_gt_pow hh
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  unfold localThreshold
  nlinarith
end ThreeSum.LocalCoverBounds
