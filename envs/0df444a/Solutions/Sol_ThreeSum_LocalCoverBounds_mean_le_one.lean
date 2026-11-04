-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.mean_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:23.960868+00:00
-- url     : https://prove2.me/submissions/dee2ef0f-15d6-4c83-ba27-0b4a168deb20

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

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {L h p : ℕ} (hp : 0 < p)
    (hlo : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : mean L h p ≤ 1 := by
  have hG : (groupSize h : ℝ) ≤ 2 ^ (2 * h) := by exact_mod_cast groupSize_le_pow h
  have hlow : (outputCount L h : ℝ) * 2 ^ (2 * h) ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast hlo
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mean, div_le_one (by positivity)]
  exact (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)).trans hlow
end ThreeSum.LocalCoverBounds
